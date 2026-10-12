# Next bounded coverage and explicit label-state handoff

Status: proposal only. No next-slice Lean literals or checker have been emitted.
The accepted pilot remains immutable and must not be replayed.

## Measured baseline and actual exercised branches

The final accepted check took 19.658341383 compiler seconds and
3,242,221,568 bytes peak VM. The successful statement/data/check roots took
38.293896272 compiler seconds in total; three preserved failed attempts took
25.082153170 additional seconds. Six final probes use only propext.

Each accepted raw interval 10851..10978 contains **41 climb-derived relabels and
87 ADDs**, not scalar-only events. All relabels reference catalog child 0,
directed 0→2 at rank 1. BRANCH_EXERCISE.json records the exact counts and first row.
It does not prove the child operator or any unexercised catalog record.

A single larger reduction would reevaluate the accepted checks, deepen its
label-update expressions and repeat common table normalization. The earlier
maxRecDepth failures are concrete evidence to prefer retained chunk certificates,
not a basis for increasing caps or predicting a speedup. No full-stream fit follows
from this one measurement.

## Exact next uncovered contiguous interval

Propose **10979..11042 inclusive, 64 rows in each orientation**. Each contains
62 ADDs and two climbs, at source indices 11036 and 11040, both 0→2, rank 1.
There is no phase, adapter, residual adapter or centre row in either interval.
NEXT_SLICE_SOURCE_PLAN.json pins the raw slice digests and individual climbs.
The immediately following work remains held; first new child key 0→3, catalog
ordinal 1, appears at source row 11135. Do not jump to it while silently assuming
the intervening label state or admissibility.

The earlier raw prefix 0..10850 and all later unselected rows remain outside this
finite certificate. In particular, its pre-A ADD/SCALE-only *label effect* does
not turn that earlier prefix into an accepted WellLabelled or physical theorem.
The full canonical projection still has 21,192 unchecked rows per orientation.

## Reuse the existing composition API

The accepted PR509Stream source already supplies:

- LemmaG.Stream.labRun_append (lines 329–332)
- LemmaG.Stream.wellLabelled_append (lines 335–341)
- LemmaG.Stream.labRun_untouched (lines 345–350)

Do not introduce another generic stream-composition induction. Use the accepted
pilot WellLabelled theorem, the next chunk's Boolean soundness result, and
wellLabelled_append to combine exactly the two lists in chronological order.

The new supplier obligation is an explicit **label-state equality**. Source-only
projection of the accepted pilot changes exactly 41 distinct L registers, each to
canonical label 2; the other 695 register labels remain initial. Both orientations
have the same proposed checkpoint. The two full equations still require proof:

    labRun (pilot.forward.map Row.event) initialLabels = checkpointLabels
    labRun (pilot.backward.map Row.event) initialLabels = checkpointLabels

The checkpoint can be a sparse 41-index override of the already accepted start
table, rather than another copied 736-element table. Prove touched-coordinate
values by bounded kernel checks, and the complement with labRun_untouched plus an
exact moved-register support fact. This avoids enumerating arbitrary payloads and
keeps the unchanged-label premise explicit. The proposed source-only checkpoint
hash is not itself either equation.

Then prove each next64 checkRows result at checkpointLabels, derive its
WellLabelled fact with the accepted checkRows_wellLabelled, and rewrite the
checkpoint equality into wellLabelled_append. Keep the accepted pilot theorem as
an imported fact; do not reevaluate its checkRows certificate. Exactly 192 A-phase
rows per orientation would then be covered, conditional on all proposed gates
passing. No such larger result is claimed now.

## Boundary adapters are separate obligations

Keep the exact omitted-row inventory. In the full source there are 1,304 endpoint
adapter, 304 residual adapter, and nine phase rows per orientation. They are not
physical identities. This next interval crosses none of them.

Any future physical-stream assembly must decode these rows as source-bound chart
transitions, keep phase/recipe-sensitive labels, and separately supply their
all-payload operator equations and equality with the canonical projection at each
boundary. No amount of canonical-frame chunk checking discharges that obligation.
A future centre slice must additionally include its real COPY/CLEAR label updates
and both directed centre chains. Label bookkeeping never supplies a clean-payload
premise or proves private erasure.

## Smallest staged experiment

Expected new sources, all reusing the current catalog and pilot objects:

1. F19CoverageNextData: sparse checkpoint data and the exact two64-row lists.
2. F19CoveragePilotBoundary: the two checkpoint equations and moved-support fact.
3. F19CoverageNextCheck: next-slice finite checks and thin composition using
   wellLabelled_append.

Proposed closure is seven local modules / four current / three pending with the
same 2,213 external source/object pairs. These are design counts, not an emitted
DFS or release. First gate only the data + boundary supplier: six/four/two.
Review that measurement before the conditional next-check seven/six/one gate.
No source emission or compiler is authorized by this plan itself.

Each compiler stays serial in one existing shared slot: 60 seconds/4 GiB hard,
45 seconds/3.5 GiB review, maxRecDepth8192 and maxHeartbeats2000000 unchanged.
Stop on any failure or review event. Smaller row counts are not a fit guarantee:
the new checkpoint proof has its own cost, which is precisely what this experiment
must measure. Do not increase limits or infer whole-family throughput.

Required evidence: exact input/data inverse audit; branch counts and child-key
histograms per slice; unchanged four prerequisite quadruples; full standard-only
probe blocks; separate data/boundary/check execution and queue times; peak VM/RSS;
and exact first/last raw indices plus the two accepted label-state handoff proofs.
