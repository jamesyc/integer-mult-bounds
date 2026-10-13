# Ordered XOR linearity and restored-basis conjugacy

The author-checked selected context at pinned source `47481c89fd30a43f8f882eb4b391e89c29273fd0` is kappa = 1661957774647029/10^18 (0.001661957774647029), as recorded in `certificates/selected-result.json` and `research/community-frontier890-audit/ASSEMBLY.json`. This contribution does not change kappa.

PR774 already formalizes XOR linearity, reversed-word compensation and arbitrary-helper/target shear correctness in TargetForest's separate legal single-source interpreter. This package does not claim a new conjugacy principle. It supplies the corresponding API directly for the existing PR590 ordered multioperand interpreter, preserving operand order and multiplicity; its linearity theorem also permits self reads. The reversal theorem retains no-self-read, and the encoded-vector/support premises are explicit.

This adds one generic Lean source with two facts for the existing ordered Boolean interpreter. `run_xor` proves that execution commutes with pointwise XOR, preserving gate order and repeated operand occurrences, including self reads. `conjugated_target_injection` proves restored-basis injection for arbitrary incoming states, using the accepted reverse-cancellation law and an explicit encoded-vector identity. No-self-read is required for that reversal step. Final preservation outside the target set follows from the original injected vector's support premise. No clean-target or clean-helper input is assumed.

The new proof imports `BitXorReversal` from PR597, which uses the exact `BitXorTargetTranslation` source published in PR590. The runtime is the pinned 317-module Lean 4.21.0 Init closure. Both new declarations have axiom sets `[propext, Quot.sound]`; eleven predecessor probe records remain separately attributable to those publications.

## Recorded check

The recovered executor compiled all three local modules freshly, retaining zero historical local outputs. All 13 ordered probe records passed. Total compiler wall time was 0.8769267650013717 seconds, including 0.24668880900026124 seconds for the new Conjugacy root. Peak sampled virtual memory was 841175040 bytes. The recorded run finished at 2026-10-13T13:13:29.378161+00:00. These are compiler measurements; the enclosing elapsed time and guards are separate. Bank independently reviewed the actual source, raw new-root log, receipts, current artifact hashes and the 317-pair/1077-edge core guard.

The original `FRESH_RESULT.json`, `SOURCE_BINDING.json`, three raw logs and three receipts are preserved byte-for-byte. `MANIFEST.json` is the earlier source/evidence checkpoint, made while review delivery was pending; its historical status is not rewritten. The later `evidence/TERMINAL_REVIEW.json` closes that scientific review. `REPLAY_SUMMARY.json` is the package's single current measured summary. No additional compilation was performed merely to copy this package. The source's historical “Source proposal, not compiled” comment is likewise preserved as part of the exact checked source bytes.

## Reproduce the three-source check

Use the exact Lean binary identified in `CORE_REFERENCE.json`. Materialize and verify every source/object identity in the referenced 317-row official core catalog before compilation. Fetch the two exact public source blobs listed in `DEPENDENCIES.json`; do not substitute the current tip of either repository. No Mathlib, Std or Batteries module is needed.

Create a fresh external directory `D` containing empty `sources`, `objects` and `logs` directories. Place the two verified public dependencies and this unchanged `BitXorConjugacy.lean` in `D/sources`. Their expected byte counts and SHA256 values are in the dependency and provenance records.

With `LEAN` set to the verified absolute binary path and `D` absolute, use these compiler arguments, in this exact order, from `D/sources`:

```sh
export LEAN_PATH="$D/objects"
export MIMALLOC_ARENA_RESERVE=64MiB
export LEAN_NUM_THREADS=1
cd "$D/sources"
"$LEAN" -s65536 -j1 -o "$D/objects/BitXorTargetTranslation.olean" "$D/sources/BitXorTargetTranslation.lean"
"$LEAN" -s65536 -j1 -o "$D/objects/BitXorReversal.olean" "$D/sources/BitXorReversal.lean"
"$LEAN" -s65536 -j1 -o "$D/objects/BitXorConjugacy.olean" "$D/sources/BitXorConjugacy.lean"
```

Run serially under a process supervisor, capture each complete stdout/stderr stream separately, stop at the first failure, and enforce the recorded per-process 60-second/4-GiB hard limits and 45-second/3.5-GiB review thresholds. The displayed compiler arguments alone are not a resource supervisor. Before and after each process, check immutable inputs and first-match import origins; after each process require its exact complete ordered probe records with only the permitted standard axioms. All 13 expected records are in `REPLAY_SUMMARY.json`. Preserve raw warnings and logs rather than deleting or normalizing them. Fresh receipts should record their own commands, paths, timing and hashes; do not rewrite the original receipts to pretend they describe a later run.

## Scope and attribution

The concrete D word, its actual helper-state adapter, the finite matrix identity, physical frames, signed-positive bounds, hosted emission/invoice and multiplication theorem remain separate obligations. In particular, this generic result does not certify or adopt the finite PR915 or PR926 candidates.

Source motivation and attribution are retained for Gareth Davidson (@bitplane), PR915 at mathematical head `7d5ef1dcf994d0542f2d302110b33780f5504ab7` and publication head `e9daefe320a0043000bd9746664ed02c3287d056`, including its stated PR794/713/716/686 restored-basis lineage. The exact PR590/597 interpreter/reversal source references and Apache-2.0 notices remain attributable to their original contributors. Prepared with OpenAI assistance. See `NOTICE.md`.
