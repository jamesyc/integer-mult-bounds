# Selected f19 label and directed-recipe coverage proposal

Status: source design only. No source generator, supplier checker, Lean compiler,
or selected finite proof was run for this proposal. No numerical witness changes.

## Exact target

Use the selected `research/direct-delivery504-global` files from source f19cb621,
whose inspected bytes remain identical in the current db0e57bc clone. The proposed
Lean goal is `SelectedCertificate selectedData`: the Boolean statement in
`F19CoverageStatement.lean` evaluates to true for independently audited literal
input data. This is decidable. `selectedData` has not been emitted.

Each of the two source programs has 22,937 rows. The canonical-frame projection
keeps 17,872 scalar, 3,432 climb, and 16 centre rows, hence 21,320 rows per
orientation. It carries each original row index and exact coefficient pair.
It checks label incidence and directed child keys/ranks. It does not interpret
operators or calculate scalar matrix columns.

Labels are the 983 canonical frame IDs. Registers are L0..727 and C0..7, encoded
as Fin736. Initial L labels come literally from `canonical.start`; initial C
labels are zero (each centre is explicitly cleared before use). A `clear`
sets its stated frame through PR509 `Event.lab`; its scalar zeroing is outside
this coverage proposition.

## Minimum trusted input decoder

Three immutable inputs suffice: CANONICAL-WORD.json.gz, LOCAL-PROGRAMS.json.gz,
and CLIFFORD-RECIPES.json. Before parsing, match their exact raw hashes in
SOURCE_PINS.json and the delivered manifest. Use strict UTF-8/JSON, reject duplicate
keys, booleans where integers are required, nonfinite values, wrong arities,
unknown tags, out-of-range indices and nonpositive denominators. Bound each
uncompressed input to 16 MiB. Do not import the upstream emitter or auditor.

Emit these exact projections, with an inverse/source-row audit:

- canonical `frames.map length` (983 entries) and `start` (728 entries);
- recipe `children` in existing order as `(old,new,rank)`, including original
  ordinal, 2,922 entries. Do not sort or deduplicate records. An emitted directed
  key must resolve unambiguously; reject duplicate `(old,new)` keys in the decoder.
- `climb(part,r,a,b,k)` maps to relabel Lr a b and its exact child ordinal/rank;
- `center(k,a,b,r)` maps to relabel Ck a b and its exact child ordinal/rank;
- scalar add/scale keep signed numerator and positive denominator as syntax;
  copy/clear keep the source frame. No reflected order or sign is invented:
  both emitted source lists are decoded literally, independently;
- preserve all dropped source indices, tags and fields in a side inventory.

Only `phase` markers (9), `adapter` rows (1,304), and `residual_adapter` rows
(304) are dropped from this projection, per orientation. They are NOT identified
with physical identity operators. The source auditor's `cur` canonical-frame
tracking likewise leaves them unchanged. Full boundary charts and paid residual
wrappers need a separate label/operator decoder; no complete physical stream
`WellLabelled` or `RecipesExact` claim follows from this projection.

The directed child catalog does not include the separate 224 endpoint-adapter
records. Rank checking here is the emitted rank versus record rank and absolute
frame-dimension difference. It is not a binary subspace inclusion/rank proof,
Clifford recipe interpretation, phase proof, or cost theorem.

## Reuse boundary

The proposed module imports the already accepted `PR509Stream` compatibility
module explicitly. Its source bytes equal the pinned cloned `LemmaG/Stream.lean`;
no silent object renaming or new upstream replay is proposed.

`admissibleB` is a finite equality decision procedure for PR509's existing
`Event.Admissible`; `checkRows` uses its unchanged `Event.lab`. A small separately
reviewed structural induction should connect a successful check to
`ProjectedWellLabelled`. Do not reprove PR509 conjugation/realization induction.
Coefficient codes deliberately have no scalar interpretation: they retain the
exact source rational syntax while label admissibility ignores coefficients.
A later rational coefficient interpretation must preserve the same event shapes.

Coverage yields directed record references for the selected relabel occurrences.
To use accepted `DirectedChildRecipes.recipesExact_of_children`, callers still
need the all-payload physical-recipe-to-child and canonical child equations for
every chosen record. Frame currently owns only literal child[7], 0→9, rank1.
Its first climb occurrence is source row 11877; that single operator proof is
not a certificate for all selected children.

Private coefficient/tableau work is not in these macro events. Fin736 does not
claim to model the full physical 7,682-family construction. Original arbitrary
dirty data/helper payloads, private erasure, zero columns, full charts, complete
owner hosting and invoices remain separate suppliers to PR516.

## Smallest proposed admission sequence

First review this spec and decoder design without compilation. After explicit
integration admission, emit a small pilot of the first 128 A-phase rows in each
orientation: source indices 10851..10978, initial canonical labels unchanged by
the preceding scalar/adapter projection. Keep the full skinny 2,922-key catalog,
983 dimensions and 728 start labels, not full monomial recipe bodies.

Expected pilot closure: existing PR509Stream plus three proposed new roots
(spec, literal pilot data, finite pilot check), four local modules total with
one current and three pending, and the already accepted external cache boundary.
These are proposal counts, not a fresh dependency audit. Use the existing single
shared-slot checker, 60-second/4-GiB hard and 45-second/3.5-GiB review limits only
after admission. No fit claim is made. Stop after the pilot measurement.

The full 42,640-row check would require a separately reviewed bounded chunk plan
with exact label-state boundary joins. Do not emit or launch the full family from
this proposal. Do not scan scalar columns, rerun Clifford generation, adopt an
unmerged PR567–571 provider, or add an external dependency.

## Attribution

The selected emitter retains icekylinx's PR425/433 and DreamingOfClouds' modified
PR514 lineage; the selected independent auditor is the attributed local extraction
for icekylinx. PR509 Stream is by DreamingOfClouds with Claude assistance. This
proposal adds only a selected-source structural coverage boundary, with OpenAI
assistance, under the repository's Apache-2.0 license. It makes no new κ claim.
