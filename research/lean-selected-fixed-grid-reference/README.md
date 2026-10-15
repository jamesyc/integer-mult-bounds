# Selected first-three-row reference execution on one fixed grid

This package adds four checked Lean 4.21.0 modules above the existing exact reference-arithmetic sources. It follows the selected forward rows

1. `SCALE(119, -1/2)`
2. `ADD(119, 169, +1/2)`
3. `ADD(169, 119, -1)`

through their actual finite reference instruction lists, including memory outside the written blocks and the visible accumulator. The new fixed-denominator interpreter represents every prefix at `Q = P + 1` under explicit initial bounds. No rounding occurs in this interpreter: the exponent bound proves the parity required by integer halving.

## Author-checked context

The contextual selected-main value is **κ = 836330098538459 / 500000000000000000 = 0.001672660197076918**, checked against source context `0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2`. These modules do not establish the multiplication theorem or its exponent saving. They supply a finite semantic prerequisite for the selected implementation.

## Four additions

- `Current1094Rows12DyadicReference` composes the already checked SCALE and ADD traversals. Its `16*n` reference instructions update each target to the exact raw Cell `addCell (minusHalfCell t) (halfCell u)`. The source block and outside cells are preserved. It proves full-state decoding at every prefix and a per-output budget from the original numerator/exponent bounds.
- `Current1094Rows12PrefixBitBudget` follows the actual instruction prefixes, including the dirty initial accumulator. On the two finite active blocks and accumulator, numerator magnitude below `2^b` and exponent at most `P` imply magnitude below `2^(b+P+1)` and exponent at most `P+1` throughout. This bound is independent of the number of components and prefix length; unrelated memory need not be bounded.
- `FixedGridReference` maps a raw Cell `(z,p)` to the integer `z * 2^(Q-p)` and gives an integer interpreter for the existing instruction type. `step_encode` and `run_encode` prove instruction/prefix compatibility under the explicit exponent conditions. `half_factor`, `half_even` and `half_exact` derive exact integer halving; `add_exact` relates aligned addition. The selected rows1–2 theorem supplies `Q=P+1` from the preceding prefix bound.
- `SelectedFirstButterflyReference` appends the actual third-row subtraction traversal and counts `24*n` reference instructions. It proves both raw Cell endpoints, outside-memory preservation and fixed-grid refinement for every prefix. For input values `(t,u)`, the two output values are `((u-t)/2,(u+t)/2)`. If `H0(t,u)=((t+u)/2,(t-u)/2)`, this is the signed output permutation `J(H0(t,u))`, where `J(a,b)=(-b,a)`. This port/sign convention is explicit.

All four source files are unchanged accepted bytes. Older source comments saying “candidate” or “initially uncompiled” describe their preserved preparation history; `ACCEPTANCE.json` records the later completed source-bound checks.

## Reuse and nonduplication

[PR2025](https://github.com/CrocSwap/integer-mult-bounds/pull/2025), exact head `c8005ae112094a33c3158e87baf257da8999568d`, already supplies row-one scalar/flat/Cell semantics and aligned `addCell`. [PR2370](https://github.com/CrocSwap/integer-mult-bounds/pull/2370), exact head `9db8170ed82cd0d96b696d3fb7ba4c839daef884`, already supplies family blocks, row-two ADD refinement and a generic finite trace budget. Their source modules are fetched as pinned prerequisites, never copied into this package. The only direct external research import of the four-root chain is `Current1094Row2DyadicReference` from PR2370.

The additions prove the actual two-row composition, its sharper all-prefix bound, fixed-grid instruction simulation and the subsequent third-row endpoint. They reuse the existing Cell arithmetic and traversal proofs. `PUBLIC_SOURCE_MANIFEST.json` names the complete 15-module public prerequisite closure, including exact existing header adaptations and attribution. There are four new Lean files, totaling 50,076 bytes.

The supplied chronological reserve arguments in [PR2390](https://github.com/CrocSwap/integer-mult-bounds/pull/2390) and [PR2327](https://github.com/CrocSwap/integer-mult-bounds/pull/2327), and the generic common-grid reserve analysis in [PR2284](https://github.com/CrocSwap/integer-mult-bounds/pull/2284), are credited background. This finite instruction refinement neither duplicates their recursive reserve argument nor claims to instantiate the all-size selected execution assumptions.

## Acceptance and exact scope

The four roots have 30 standard-only axiom probes and six complete printed types. Each was independently source/API and terminal reviewed by the machine-contracts peer; the accepted runs have no warnings or errors. The public acceptance summary binds every result to its exact source hash. Failed proof-normalization attempts and their exact corrections remain in the authors’ local evidence. No publication replay is claimed.

The results quantify over all finite component counts and all instruction prefixes of the named reference programs, including empty and overlong prefixes. Quantitative statements retain their initial finite-footprint/accumulator bounds. Generic source and target blocks must be distinct. Real decoding of the fixed-grid projection is asserted only on bounded cells; the full integer projection can still be defined elsewhere without asserting that it preserves their real values.

The `16*n` and `24*n` counts are reference instruction lengths. The package does not price primitive bit operations, construct physical input words, choose a global precision schedule, restore scratch, pack outputs, prove a full selected layer, identify completed rounded transform arrays, or derive a root-uniform recurrence constant. The separately developed finite-symbol butterfly and Program/Host bridge are later consumers of this semantic boundary.

## Reproduction and attribution

See `REPRODUCTION.md` and `check.py`. The checker uses a prepared official Lean/Mathlib installation, fetches only the pinned public source prerequisites, verifies source identities, and preserves build logs. It does not install a toolchain or rebuild official dependencies.

The new modules retain their original author and Apache-2.0 notices, including OpenAI assistance. The prerequisite manifest preserves the existing attribution for the LemmaG/LemmaA, prefix-norm, component-store, scalar/flat-reference and selected routing work. Reconstruct only the documented single `FreshScalarSupportStream` namespace closure.
