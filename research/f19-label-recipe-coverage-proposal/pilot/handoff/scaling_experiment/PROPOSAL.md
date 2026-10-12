# One batched coverage and reduction-cost experiment

Status: source-inspection proposal only. No new Lean implementation, activation,
compiler call, or broad enumeration is included. The seven accepted modules and
192 projected rows per orientation are retained unchanged.

## What the existing evidence actually says

The last 64-row-per-orientation check cost 11.280783303 compiler seconds,
0.000842804 FIFO seconds, and 3,108,790,272 bytes peak VM. Its seven goals passed.
The sparse checkpoint supplier cost 4.627112730 seconds and 3,243,335,680 bytes VM.
These are whole-module measurements, not a full-stream throughput model.

Direct inspection of F19CoverageStatement identifies two separate reduction
paths. Each ADD performs label equality in both admissibleB and scalarAnnotationB,
with five syntactic label reads in total. The accepted 62-ADD/two-relabel slice
therefore has 312 such reads per orientation. Reads traverse the sparse 41-index
membership test, then possibly the original array and subsequent functional
updates. Separately, childReferenceB reads the 2,922-entry child array and
983-entry dimension array. The previous logs do not measure which path dominates.
Syntactic counts must not be presented as kernel operation counts or timings.

The installed Lean 4.21 decide +kernel implementation uses mkAuxLemma and caches
the checked proposition; imported proofs do not need reevaluation. The installed
profiler option reports exclusive component/declaration times. Exact installed
source hashes and inspected source/slice hashes are in
SOURCE_HOTSPOT_AND_SLICE_INVENTORY.json. The proposed new check modules enable
profiler with a 100 ms threshold; no profiler output file or resource increase is
needed. If its output cannot distinguish the reductions, the result is explicitly
inconclusive rather than an invented attribution.

## Compare the two approaches

1. Jointly freeze and review several fixed 64-row proofs with successive sparse
   checkpoints. This amortizes source/runtime/driver review without changing the
   trusted finite checker. It retains individual receipts and stops between roots.
   It does not itself reduce the kernel work per row or establish memory fit.
2. Prove a checker decomposition, then compare it on one new slice. Define
   labelRowsB using the existing admissibleB/scalarAnnotationB and the same
   Event.lab transitions, and childRowsB as all(childReferenceB p). Prove exactly
   checkRows p rows labels = (labelRowsB rows labels && childRowsB p rows).
   This Boolean factoring theorem reuses checkRows_wellLabelled for soundness;
   it adds no realization or append induction. It gives separate timed kernel
   certificates for label evolution and catalog/rank coverage. It may cost more.
   An Array/trie replacement or fused label predicate is deferred until this
   measurement identifies a justified target; no representation speedup is assumed.

## The single proposed experiment

Freeze one six-source packet, reviewed once as a whole. Proposed union is
13 local modules: seven current, six new, with the same 2,213 external pairs.
This is a design count, pending emitted import traversal and exact source review.

1. CheckDecomposition: the two Boolean functions and exact equality above.
2. BatchData: only the exact next two 64-row lists in each orientation and the
   proposed sparse checkpoints. It imports the accepted NextCheck and preserves
   signed raw numerator/denominator pairs and child ordinals.
3. Boundary192: both full labRun equalities after the accepted next64, using only
   that 64-row list plus the accepted starting checkpoint. Its sparse end state
   adds registers 126 and 218, giving 43 changed labels. It never reduces the
   original accepted 128-row check or reevaluates the 192-row prefix.
4. ChunkA: check raw rows 11043..11106, both orientations, then supply both full
   end-state equalities and thin 256-row composition. Each slice has 63 ADDs and
   one child0 relabel (register216, row11073). Its sparse end state has 44 changed
   labels. Reuse labRun_untouched and the accepted append theorem.
5. ChunkBDirect: check raw rows 11107..11170 at ChunkA's certified checkpoint using
   the existing checkRows, then derive the 320-row projected composition.
6. ChunkBSplit: check the identical new ChunkB rows at the identical checkpoint
   using separate labelRowsB and childRowsB kernel certificates. Combine by the
   proved equality and existing soundness theorem. ChunkBDirect and ChunkBSplit
   have identical direct imports (ChunkA plus CheckDecomposition); neither imports
   the other's result. Their isolated closures each contain 12 local modules.

The paired ChunkB measurement intentionally computes the same newly supplied
64-row obligation twice to compare proof layouts. It never rechecks the accepted
192-row prefix. Both orientations of ChunkB contain 56 ADDs and eight relabels:
four child1 (0→3, rank1, first raw11135), and four child2 (0→4, rank1, first11155).
These are genuinely new catalog keys. The resulting 320 projected rows per
orientation, if all checks pass, contain 268 ADDs and 52 relabels.

## Admission, resource bound, evidence and stopping condition

After exact source/literal/equivalence and one binding review, admit only these
six named new roots, serially through one existing shared slot. Keep 60 seconds/
4 GiB hard and 45 seconds/3.5 GiB review limits per module, maxRecDepth8192 and
maxHeartbeats2000000. Keep all source/owner locks and current/runtime guards.
Stop on the first failure or review event and preserve every preceding PASS.
No automatic retry, batch enlargement, cap increase or subsequent packet follows.

Completion is six terminal measurements (or the first stop), exact current/probe
audit, and a same-slice Direct/Split comparison if both ran. Report each component's
compiler/FIFO/VM/RSS measurements, profiler attribution, review latency and source
preparation cost. A faster split on this one slice is only local evidence; a
slower or unresolved split remains a useful result and need not replace the old
checker. No numerical performance threshold is a scientific correctness premise.

All new raw intervals are contiguous and contain no omitted macro row. Preserve
the existing omitted-adapter inventory. Earlier-prefix admissibility, later
centre COPY/CLEAR branches, phase/Clifford operator correctness, expanded physical
work registers and full-stream/whole-owner endpoints remain separate obligations.
The proposal does not turn projected label continuity into any of those claims.
