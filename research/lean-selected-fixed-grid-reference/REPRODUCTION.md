# Reproduce the source-bound checks

The package requires an already prepared official Lean 4.21.0 installation and the cached Mathlib checkout at `308445d7985027f538e281e18df29ca16ede2ba3`, with the eight package revisions in `PUBLIC_SOURCE_MANIFEST.json`. Python 3, Git and a Unix host supporting `resource` and `fcntl` are required. No installation or official dependency rebuild is performed.

Run from this package directory:

```sh
python3 check.py --verify-package
```

This command checks only the four shipped source hashes, import order, public dependency identities, acceptance bindings and exact probe/type declarations. It neither fetches sources nor invokes Lean.

To perform a new reproduction after making the matching cached environment available:

```sh
export LEAN_HOME=/path/to/lean-4.21.0
export MATHLIB_HOME=/path/to/matching/mathlib
export LEAN_REPLAY_LOCK=/path/to/shared-replay.lock
python3 check.py
```

The checker clears inherited `LEAN_OPTS` and `LEAN_PATH`, verifies the Lean version and all pinned Git heads, acquires the supplied exclusive lock, and makes a fresh work directory. It fetches public prerequisites at immutable commits, checks their Git blobs and SHA-256 hashes, and applies only the manifest’s two attributed one-line import replacements. It then compiles the 15 prerequisite research modules and the four shipped modules in the listed order. Existing official objects are used directly.

Each compiler uses one worker, a 60-second timeout and a 4-GiB address-space limit. At least 8 GiB of free space is required. Default elaboration heartbeat limits are unchanged. Any missing prerequisite, byte mismatch, timeout or failed root stops the run. Sources, objects, stdout, stderr and exit codes are retained in the fresh work directory; no failure is converted into acceptance. Warnings from reused prerequisites are preserved. The four shipped roots are checked against the exact axiom probe list, standard axiom set and complete type output, and must have no diagnostics.

Only the four original completed root checks are claimed in `ACCEPTANCE.json`. Preparing or syntax-checking this reproduction script is not another Lean replay. The original proof sources and accepted evidence are unchanged.
