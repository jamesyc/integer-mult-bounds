# T37 native finite moment certificate

This checkpoint contains the accepted finite rational certificate for the PR942 T37 native complex branch at upstream main `bbc600db2fc15007b7c914f4f2b2ed55fa909c87`.

Author-checked selected context: **κ = 1661960547713947 / 1000000000000000000 = 0.001661960547713947**. This is the source certificate's selected value, not a complete Lean theorem about multiplication complexity.

## Checked result

The seven source-ordered rank/count rows are
`(1,848490), (2,112554), (3,148518), (4,53946), (5,23976), (8,2664), (48,11086)`.
Their total count is 1,201,234 and rank mass is 2,408,256. The dimension is 73, live count 33,152 and deficit 11,840.

At
`b = 416181814685169713943 / 250000000000000000000000`,
the exact finite log/exponential upper construction, with one ordinary outward ceiling, equals

`199999999999999999999999932761 / 200000000000000000000000000000`.

Its residual below one is
`-67239 / 200000000000000000000000000000`.
This selected native branch has no fallback term. The bit and conservative branches use different formulas and are not replaced by this result.

The five exported facts check profile totals, arithmetic domains, the rounded value, equality to the pinned certificate, and strict inequality below one. The 21 exponential blocks and 60 finite decisions use kernel-checked rational arithmetic.

## Actual compiler evidence

Lean 4.21.0 accepted this exact source in one fresh compiler invocation:
- Compiler: 1.369667870 seconds.
- Peak virtual memory: 708,132,864 bytes.
- Whole launcher invocation: 2.479080217 seconds.
- Before/after current guards: 0.547059475 / 0.500946927 seconds.
- Five ordered axiom probes: one axiom-free; four using only `propext`, `Classical.choice`, and `Quot.sound`.
- New object SHA256: `0a27464ccde1b0dc05447c9bd3d6968443f496df1ea63c3bc4ea6fe00229284e`.

The closure contains this one fresh root, two retained roots and 319 cached runtime modules. The complete receipt, raw log, exact frozen configuration and independent terminal review are preserved here. The frozen configuration records the actual recovery-machine paths; this small checkpoint does not add a portable public replay checker or duplicate cached objects.

The retained `SelectedMomentLogCheckpoints` and `SelectedMomentUpperAggregate` sources originate from [PR585's exact public commit](https://github.com/jamesyc/integer-mult-bounds/tree/809915a264d4fbe1f7597cc13da3610dc4d52f15/research/lean-selected-rational-certificates). Their freshly recovered object and receipt identities are recorded in the frozen configuration.

## Scope and provenance

The exact source assembly is [ASSEMBLY.json at the pinned main](https://github.com/CrocSwap/integer-mult-bounds/blob/bbc600db2fc15007b7c914f4f2b2ed55fa909c87/research/community-frontier942-audit/ASSEMBLY.json), SHA256 `4b2894956e594e408e111d806c842f2ed2c32aefcadff93fad69ff0b46f1991a`. Source preparation used read-only reconstruction of its fixed assembler edits; it did not execute the supplier or assembler.

`SOURCE_BINDING.json` is the original preflight record and deliberately retains its pre-compilation status and `kernel_checked: false`. The later `FRESH_RESULT.json` and `TERMINAL_REVIEW.json` record the actual accepted check.

A Real enclosure, justification for the native no-surcharge license, provider/profile and physical realization, recurrence and integer-rounding bounds, bit-supplier validity, bootstrap, outer inequalities and an all-size multiplication theorem remain separate obligations. This certificate does not discharge them.

Prepared with OpenAI assistance. No new axioms or external arithmetic oracle are used by the Lean proofs.
