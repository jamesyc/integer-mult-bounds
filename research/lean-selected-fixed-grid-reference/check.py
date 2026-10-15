#!/usr/bin/env python3
"""Source-bound reproduction; requires an existing matching official cache."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def checked_bytes(path, size, digest):
    data = Path(path).read_bytes()
    require(len(data) == size and sha256(data) == digest, f"Source mismatch: {path}")
    return data


def command(*args):
    return subprocess.check_output(args)


def verify_package(manifest, acceptance):
    shipped = manifest["shipped_modules"]
    deps = manifest["public_prerequisites"]
    modules = {x["module"] for x in deps + shipped}
    order = manifest["compile_order"]
    require(len(modules) == len(order) == len(deps) + len(shipped), "Duplicate or missing module")
    require(set(order) == modules, "Compile order does not cover the exact closure")
    accepted = {x["module"]: x for x in acceptance["modules"]}
    require(set(accepted) == {x["module"] for x in shipped}, "Acceptance module mismatch")
    for item in shipped:
        data = checked_bytes(ROOT / item["path"], item["bytes"], item["sha256"])
        require(blob(data) == item["git_blob"], "Shipped Git blob mismatch")
        text = data.decode()
        imports = re.findall(r"^import (\S+)", text, re.M)
        require(imports == item["imports"], "Shipped import mismatch")
        for dep in imports:
            require(dep in modules and order.index(dep) < order.index(item["module"]), "Import order mismatch")
        audit = accepted[item["module"]]
        require(audit["source_sha256"] == item["sha256"] and audit["source_bytes"] == item["bytes"], "Acceptance source mismatch")
        probes = re.findall(r"^#print axioms (\S+)", text, re.M)
        types = re.findall(r"^#check @(\S+)", text, re.M)
        require(probes == [x["declaration"] for x in audit["probes"]], "Probe list mismatch")
        require(len(types) == audit["printed_type_count"], "Printed type count mismatch")
        require(all(name + " :" in audit["printed_full_types"] for name in types), "Missing complete accepted type")
    require(sum(len(x["probes"]) for x in accepted.values()) == 30, "Wrong total probe count")
    require(sum(x["printed_type_count"] for x in accepted.values()) == 6, "Wrong total type count")
    for item in deps:
        require(re.fullmatch(r"[a-zA-Z0-9_.-]+/[a-zA-Z0-9_.-]+", item["repository"]) is not None, "Invalid repository")
        require(re.fullmatch(r"[0-9a-f]{40}", item["commit"]) is not None, "Unpinned prerequisite")
        require(".." not in Path(item["path"]).parts and not Path(item["path"]).is_absolute(), "Invalid public path")
    return accepted


def compile_limits():
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, 4 * 1024**3))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-package", action="store_true", help="Check shipped metadata/bytes only; no network or compiler")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "PUBLIC_SOURCE_MANIFEST.json").read_text())
    acceptance = json.loads((ROOT / "ACCEPTANCE.json").read_text())
    accepted = verify_package(manifest, acceptance)
    if args.verify_package:
        print("PASS: four shipped sources, exact dependency order, 30 probes and six type bindings")
        return
    lean_home = Path(os.environ["LEAN_HOME"]).resolve()
    mathlib = Path(os.environ["MATHLIB_HOME"]).resolve()
    lock_path = Path(os.environ["LEAN_REPLAY_LOCK"])
    lean = lean_home / "bin/lean"
    env = os.environ.copy()
    env.pop("LEAN_OPTS", None)
    env.pop("LEAN_PATH", None)
    version = subprocess.check_output([str(lean), "--version"], env=env, text=True)
    require(re.match(r"Lean \(version 4\.21\.0(?:[,)]| )", version) is not None, "Lean version mismatch")
    revisions = [(mathlib, manifest["runtime"]["mathlib_commit"])]
    revisions += [(mathlib / ".lake/packages" / x["name"], x["commit"]) for x in manifest["runtime"]["official_package_commits"]]
    for path, head in revisions:
        require(command("git", "-C", str(path), "rev-parse", "HEAD").decode().strip() == head, f"Revision mismatch: {path}")
        require(not command("git", "-C", str(path), "status", "--porcelain", "--untracked-files=no").strip(), f"Tracked changes: {path}")
    with lock_path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        work = Path(tempfile.mkdtemp(prefix="selected-fixed-grid-reference-"))
        print(f"Sources, objects and all logs retained in {work}", flush=True)
        for name in ["sources", "objects", "logs", "upstream"]:
            (work / name).mkdir()
        command("git", "init", "-q", str(work / "upstream"))
        fetched = set()
        for item in manifest["public_prerequisites"]:
            key = (item["repository"], item["commit"])
            if key not in fetched:
                command("git", "-C", str(work / "upstream"), "fetch", "--no-tags", "--depth=1", "https://github.com/" + key[0] + ".git", key[1])
                fetched.add(key)
            data = command("git", "-C", str(work / "upstream"), "show", item["commit"] + ":" + item["path"])
            if "replacement" in item:
                require(len(data) == item["upstream_bytes"] and sha256(data) == item["upstream_sha256"] and blob(data) == item["upstream_git_blob"], "Upstream adapted source mismatch")
                patch = item["replacement"]
                before, after = patch["before"].encode(), patch["after"].encode()
                require(data.count(before) == patch["count"] == 1, "Import adaptation mismatch")
                data = data.replace(before, after, 1)
            elif "git_blob" in item:
                require(blob(data) == item["git_blob"], "Public Git blob mismatch")
            require(len(data) == item.get("derived_bytes", item.get("bytes")) and sha256(data) == item.get("derived_sha256", item.get("sha256")), "Public source hash mismatch")
            (work / "sources" / (item["module"] + ".lean")).write_bytes(data)
        for item in manifest["shipped_modules"]:
            data = checked_bytes(ROOT / item["path"], item["bytes"], item["sha256"])
            (work / "sources" / (item["module"] + ".lean")).write_bytes(data)
        libraries = [work / "objects", mathlib / ".lake/build/lib/lean"]
        libraries += [path / ".lake/build/lib/lean" for path, _ in revisions[1:]]
        env["LEAN_PATH"] = ":".join(map(str, libraries))
        for module in manifest["compile_order"]:
            require(shutil.disk_usage(work).free >= 8 * 1024**3, "Need at least 8 GiB free")
            out = work / "logs" / (module + ".stdout")
            err = work / "logs" / (module + ".stderr")
            with out.open("wb") as stdout, err.open("wb") as stderr:
                try:
                    result = subprocess.run([str(lean), "-s65536", "-j1", "-o", str(work / "objects" / (module + ".olean")), str(work / "sources" / (module + ".lean"))], env=env, stdout=stdout, stderr=stderr, timeout=60, preexec_fn=compile_limits)
                    code = result.returncode
                except subprocess.TimeoutExpired:
                    code = 124
            (work / "logs" / (module + ".exit-code")).write_text(str(code) + "\n")
            require(code == 0 and (work / "objects" / (module + ".olean")).is_file(), f"Failed root {module}; logs retained in {work}")
            if module in accepted:
                text = out.read_text()
                require(not err.read_bytes(), f"Unexpected stderr for {module}")
                require(not any(x in text for x in ["error:", "warning:", "sorryAx", "⋯", "..."]), f"Unaccepted diagnostic/truncation in {module}")
                pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
                probes = [{"declaration": m[1], "axioms": [a.strip() for a in (m[2] or "").split(",") if a.strip()]} for m in re.finditer(pattern, text)]
                require(probes == accepted[module]["probes"], f"Probe mismatch in {module}")
                require(all(set(x["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"} for x in probes), "Nonstandard axiom")
                actual_types = re.sub(pattern, "", text).strip()
                normalize = lambda s: " ".join(s.split())
                require(normalize(actual_types) == normalize(accepted[module]["printed_full_types"]), f"Full type mismatch in {module}")
        print("PASS: exact research closure and source-bound root probes/types")


if __name__ == "__main__":
    main()
