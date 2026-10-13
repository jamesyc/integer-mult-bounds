# Lean finite PR1042 native moment certificate

This checkpoint contains one kernel-checked rational certificate for the
historical PR1042 T16 native profile at main
`ba82555c64e1879e4b7decce28186f208fcb8262`.

Author-checked conditional source context:
`kappa = 1672188119205421/10^18 = 0.001672188119205421`.
The exact [source assembly](https://github.com/CrocSwap/integer-mult-bounds/blob/ba82555c64e1879e4b7decce28186f208fcb8262/research/community-frontier1042-audit/ASSEMBLY.json)
has SHA256
`093f35445812ea96fe1bfe6a3af7d769cb7f274e08f4fb30f71a17ed1161e54e`.

By the time this checkpoint was prepared, main
`ce7ad1b6ab09452c3478723a2e96ed5ff212dc08` selected PR1094. Its separately
author-checked recorded kappa is
`836330098538459/500000000000000000 = 0.001672660197076918`.
That change does not repin this PR1042 certificate or establish PR1094's bound.

## Exact coverage

The supplied profile has ranks 1, 2, 3, 4, 5, 7, 8, 16, 48 with counts
349577, 60193, 62608, 20448, 11808, 3, 1152, 47, 4850.
The total count is 510686, rank mass is 1041408, dimension is 73, live width
is 14336, and rank deficit is 5120. The supplied native endpoint is
`418747253984418082117/250000000000000000000000`.

The five public facts prove exact profile totals, the rational source
domains, the source-ordered nine-term ordinary rounded upper, its equality
to the recorded residual, and its strict inequality below one. The upper is
`999999999999999999999997611023/10^30`, with residual `-2388977/10^30`.
All 27 four-step exponential blocks are connected to the exact recurrence.
There are 76 ordinary kernel decisions. One outward ceiling is applied to
the complete weighted sum. The selected native branch has no fallback term;
the separate bit and conservative source branches retain their own treatment.

The root imports only `SelectedMomentUpperAggregate`, whose dependency is
`SelectedMomentLogCheckpoints`. The accepted PR585 unit identities suffice
for rank7 (73/56, z=17/129) and rank16 (73/64, z=9/137).
No new logarithm-unit root was needed.

## Measured check and evidence

One fresh root and two retained local roots used 319 freshly verified runtime
pairs, with 322 reachable nodes and 1086 ordered import edges.
The original invocation on 2026-10-13 ran from 19:01:40.462146 to
19:01:42.261711 UTC and passed in 1.799550335 compiler seconds.
Peak virtual memory was 708149248 bytes; peak RSS was 335237120 bytes.
The before/after guards took 0.571555919 and 0.535895990 seconds separately.
Whole-wrapper elapsed time was not recorded.

All five complete ordered probes are clean: profile_totals is axiom-free,
and the other four use only propext, Classical.choice and Quot.sound.
Both guards preserved all 1710 protected hashes and eight worktree states,
including the accepted T37 native, bootstrap and outer artifacts.
There was no retry.

The source, source binding, frozen manifest, full fresh receipt, raw log
and independent terminal review are included here. The manifest preserves
the actual machine-local command and paths; this is a measured checkpoint,
not a new portable replay driver. Binary objects are not included.
Object SHA256:
`b177d366fb95a41bc185ba455ab871de94db53c31595e5b0b1800c29a12d290a`.

The environment was Lean 4.21.0, binary SHA256
`cbf5fd536e142ef1beaccf33f788fd8a7f3f29fb214e75c11319a8d8677b4b2b`,
with the exact finite runtime subset derived from mathlib commit
`308445d7985027f538e281e18df29ca16ede2ba3`.
The two retained prerequisites have actual fresh recovery receipts bound
to terminal `22d33d39bd7f86a9fc0862a9efbefd8a2358e6726d350cba4f4786091ef0dc22`.

## Scope and attribution

These are finite rational facts. The supplied profile and endpoint,
Real log/exp enclosures, native exact-cover recurrence license, saving
validity, provider/operator/physical realization, PR589 bit validity,
bootstrap, outer inequalities, precision/tape, all-size transfer and the
complete selected-kappa multiplication theorem remain separate obligations.

The proof retains the PR361 base-two engine lineage and the accepted
PR585/PR942 rational proof interfaces. PR1042 supplies the T16 profile and
caller. Historical T37 source and results are preserved. Prepared with
OpenAI assistance; no supplier execution, native oracle, or additional axiom
was used in this check.
