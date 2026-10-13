#!/usr/bin/env python3
"""Prepare the exact PR1094 Real bridge from the accepted PR799 template; never run Lean."""
from pathlib import Path
import hashlib, json, sys
template, outdir = map(Path, sys.argv[1:3])
raw = template.read_bytes()
assert hashlib.sha256(raw).hexdigest() == "0881f16da93e47ed521474977db174c092cab34556512e9c8d90ba7c62b59ac2"
original = raw.decode()
marker = "namespace CurrentMain.Current799NativeRealEnclosure"
body = original[original.index(marker):]
edits = json.loads("[{\"before\":\"Current799\",\"after\":\"Current1094\",\"occurrences\":3},{\"before\":\"open SelectedRoundedLogEnclosure Current741LogRealEnclosure\",\"after\":\"open SelectedRoundedLogEnclosure\",\"occurrences\":1},{\"before\":\"  have hu29 : Real.log (((117+29 : Nat) : ℝ)/((117-29 : Nat) : ℝ)) ≤\\n      (unitUpper 29 117 : ℝ) := by\\n    convert log_seventy_three_forty_four_upper using 1 <;> norm_num\",\"after\":\"  have hu17 : Real.log (((129+17 : Nat) : ℝ)/((129-17 : Nat) : ℝ)) ≤\\n      (unitUpper 17 129 : ℝ) := by\\n    convert log_73_56_upper using 1 <;> norm_num\",\"occurrences\":1},{\"before\":\"rounded_from_domain 1 183457 6 9 137 h1 hu9\",\"after\":\"rounded_from_domain 1 349604 6 9 137 h1 hu9\",\"occurrences\":1},{\"before\":\"(1 * 183457 : Nat)\",\"after\":\"(1 * 349604 : Nat)\",\"occurrences\":3},{\"before\":\"rounded_from_domain 2 24336 5 9 137 h2 hu9\",\"after\":\"rounded_from_domain 2 60192 5 9 137 h2 hu9\",\"occurrences\":1},{\"before\":\"(2 * 24336 : Nat)\",\"after\":\"(2 * 60192 : Nat)\",\"occurrences\":3},{\"before\":\"rounded_from_domain 3 30961 4 25 121 h3 hu25\",\"after\":\"rounded_from_domain 3 62585 4 25 121 h3 hu25\",\"occurrences\":1},{\"before\":\"(3 * 30961 : Nat)\",\"after\":\"(3 * 62585 : Nat)\",\"occurrences\":3},{\"before\":\"rounded_from_domain 4 13968 4 9 137 h4 hu9\",\"after\":\"rounded_from_domain 4 20448 4 9 137 h4 hu9\",\"occurrences\":1},{\"before\":\"(4 * 13968 : Nat)\",\"after\":\"(4 * 20448 : Nat)\",\"occurrences\":3},{\"before\":\"rounded_from_domain 5 4032 3 33 113 h5 hu33\",\"after\":\"rounded_from_domain 5 11808 3 33 113 h5 hu33\",\"occurrences\":1},{\"before\":\"(5 * 4032 : Nat)\",\"after\":\"(5 * 11808 : Nat)\",\"occurrences\":3},{\"before\":\"rounded_from_domain 8 576 3 9 137 h6 hu9\",\"after\":\"rounded_from_domain 7 7 3 17 129 h6 hu17\",\"occurrences\":1},{\"before\":\"(8 * 576 : Nat)\",\"after\":\"(7 * 7 : Nat)\",\"occurrences\":3},{\"before\":\"rounded_from_domain 44 1 0 29 117 h7 hu29\",\"after\":\"rounded_from_domain 8 1152 3 9 137 h7 hu9\",\"occurrences\":1},{\"before\":\"(44 * 1 : Nat)\",\"after\":\"(8 * 1152 : Nat)\",\"occurrences\":3},{\"before\":\"rounded_from_domain 48 2396 0 25 121 h8 hu25\",\"after\":\"rounded_from_domain 48 4866 0 25 121 h8 hu25\",\"occurrences\":1},{\"before\":\"(48 * 2396 : Nat)\",\"after\":\"(48 * 4866 : Nat)\",\"occurrences\":3},{\"before\":\"73 * 7168\",\"after\":\"73 * 14336\",\"occurrences\":24},{\"before\":\"((73 : ℝ)/8)\",\"after\":\"((73 : ℝ)/7)\",\"occurrences\":3},{\"before\":\"((73 : ℝ)/44)\",\"after\":\"((73 : ℝ)/8)\",\"occurrences\":3},{\"before\":\"roundedLog 3 9 137\",\"after\":\"roundedLog 3 17 129\",\"occurrences\":3},{\"before\":\"roundedLog 0 29 117\",\"after\":\"roundedLog 3 9 137\",\"occurrences\":3}]")
for edit in edits:
    assert body.count(edit["before"]) == edit["occurrences"]
    body = body.replace(edit["before"], edit["after"])
back = body
for edit in reversed(edits):
    back = back.replace(edit["after"], edit["before"])
assert back == original[original.index(marker):]
prefix = "import Current1094NativeUpperAggregate\nimport SelectedMomentExpEnclosure\nimport SelectedRoundedLogEnclosure\n\n/-!\nPR1094 rare-pattern T16 native Real moment at exact main\nce7ad1b6ab09452c3478723a2e96ed5ff212dc08. Eight complete weighted terms\nfollow the source-bound overlay profile and accepted finite predecessor.\nThe accepted PR799 binary reduction, Nat.cast_one normalization, generic\nexponential enclosure and outward ceiling are reused. Rank7 uses the\nexisting log(73/56) unit; no rank44 unit or new unit proof is needed.\nThe selected native branch has one ordinary ceiling and no fallback term.\n\nAuthor-checked conditional source context:\nkappa=836330098538459/500000000000000000=0.001672660197076918.\nNative recurrence license and saving/profile/operator/provider/physical\nrealization, bit validity, bootstrap/outer interpretation, precision/tape\nand all-size multiplication remain separate. This proposed source is\nuncompiled in the recovered environment; no runtime recovery is inferred.\nAttribution: inherited PR361 engine, PR585/PR605 generic certificates,\naccepted PR799 Real proof template, and PR1094 rare-pattern overlay.\nPrepared with OpenAI assistance; no supplier execution or oracle.\n-/\n"
source = (prefix + body).encode()
assert len(source) == 12166
assert hashlib.sha256(source).hexdigest() == "03877a492cac78ad1a3a7ed6dee56d645acd9c6e7e13d95726378792f241ba87"
assert source.count(b"#print axioms") == 3
assert b"decide +kernel" not in source
outdir.mkdir(exist_ok=False)
with (outdir / "Current1094NativeRealEnclosure.lean").open("xb") as f:
    f.write(source)
print(json.dumps({"source_bytes":len(source),"source_sha256":hashlib.sha256(source).hexdigest(),"ordered_body_edits":len(edits),"body_inverse_exact":True,"compiler_executed":False}))
