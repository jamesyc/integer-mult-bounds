# Bounded canonical-label pilot implementation

This is authored source and exact literal data, awaiting independent review and
compiler admission. It certifies nothing until the proposed Lean gates pass.

The sole finite goal is `checkPilot PilotData.data = true`. This checks raw
zero-based source rows **10851 through 10978 inclusive**, in forward and backward
LOCAL-PROGRAMS, 128 rows each. The separate exact-index theorem exposes that range.
The supplied label initializer is the literal 728-entry `canonical.start` table,
with arbitrary bookkeeping label 0 for the eight untouched C registers. A label
is not a payload; there is no clean or independent dirty-data premise.

All retained pre-A projection rows have tags add or scale, which PR509 Event.lab
leaves unchanged. The decoder records that structural fact and the exact excluded
phase/adapter rows in DECODER_AUDIT and OMITTED_ROWS. This establishes the source
boundary for starting this canonical projection at the pinned table. It does not
identify any omitted physical adapter with identity, and is not a theorem about
the complete emitted physical prefix. These distinctions survive the final theorem.

`decode_pilot.py` reads only the three pinned JSON/gzip payloads, with 16 MiB
uncompressed bounds, duplicate/nonfinite/schema/range checks and exact signed
numerator/denominator retention. It emits the 983 dimensions, 728 starting labels,
2,922 ordered child keys, and only the selected 256 rows. It rejects ambiguous
child keys. The raw backward coefficient `(2, -1)` is retained as a regression
example; no coefficient normalization or arithmetic matrix replay occurs.

LITERAL_PROJECTION contains the complete skinny tables, raw selected rows and
their typed decoder projection, for an independent inverse/source-row audit.
That audit is separate from the Boolean-to-PR509 soundness proof in the statement
module. Seven negative parser controls were rejected. Generation took about
0.34 seconds and 67.4 MB peak RSS under 20 CPU seconds, 30 wall seconds and
512 MiB address-space bounds. Exact measured values are in DECODER_AUDIT.

Proposed serial compiler scope: PR509Stream preserved current; then
F19CoverageStatement, F19CoveragePilotData, F19CoveragePilotCheck, in that order.
Four local modules / one current / three pending; no new external imports beyond
PR509Stream's already accepted source/object boundary. Each requested compile
uses the existing shared checker: 60 seconds / 4 GiB hard, 45 seconds / 3.5 GiB
review, stop on first failure or review event. No unchanged retry or automatic
expansion. Data source is 82,366 bytes; no runtime fit is inferred from that size.

Future full projection checking, adapter labels, binary rank/inclusion,
all-payload recipe interpretation, exact phases, scalar columns, private erasure,
whole-owner hosting and cost remain open. No new kappa is claimed by this pilot.
