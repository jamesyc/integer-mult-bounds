# Directed child recipe interface

Status: source proposal only. No Lean check or selected finite certificate is claimed.

This small interface connects interpreted directed Clifford child recipes to the existing PR509 recipe/conjugation API. It adds no event induction and does not establish a multiplier bound.

## Contract

A child stores its rank and interpreted left/right linear equivalences. A null right side is equivalent to rank zero. Evaluation is right, the supplied block of the declared rank, then left; rank zero executes left alone.

The caller provides:
- a directed lookup covering every relabel in the actual stream;
- equality of the actual recipe execution to the interpreted child;
- equality on every payload to the new canonical operator after the inverse old operator;
- the stream's complete label invariant.

The conclusion is the existing arbitrary-input PR509 conjugation identity. The two operator equalities are explicit proof obligations, not a finite certificate or conclusions of this package.

## Exact source correspondence

At integer-mult-bounds commit f19cb621be2caf3a7291a37c343c1c55afe935e0:
- `research/direct-delivery504-global/vendor/clifford/clifford_exact.py`, SHA256 `2982ead07721e83358dc67c6f49c2b4c16a236a6bebdfd72f58221be1f5d0962`: lines69–80 fix chronological composition and adjoint; lines127–149 fix phase-carrying normal forms and child order.
- `research/direct-delivery504-global/code/phases_delta.py`, SHA256 `15723107eff03013b2e797fd9fa3635b1b46c5d1c8112d19fada98c178d4acb6`: lines118–129 lower direct old/new canonical frame pairs.

The source's Fourier block is a product of Gaussian gates C=((1+i)I+(1-i)X)/2. Neither ordinary normalized Hadamard gates nor a reversed child key may be substituted. This proposal takes the interpreted block family as an explicit input and does not prove its source identity.

Raw monomial decoding must preserve bit order, affine permutation direction, the upper-triangular quadratic phase convention, and global phase. If p(x)=Gx xor offset, its intended basis action is |x> ↦ i^(phase+qvalue(x)) |p(x)>; on payload functions the phase is evaluated at the preimage address.

## Dependency and proposed check

`DirectedChildRecipes.lean` imports the already checked local module alias `PR509Stream`. That dependency is byte-identical to `research/e8-lemma-g-lean/LemmaG/Stream.lean` at PR509 commit `7b9c720ecc9f483c383e7cd9c2ab81f06ee5df59`, SHA256 `7138f4b859d0574a803e99401f05ef5e0ec9eeac0eb480775cd9b86595c365f8`.

The planned check reuses that existing object and its pinned Mathlib environment. It is two local modules total: one preserved prerequisite and one new root. The upstream module name differs from this established alias; do not rename its object or silently substitute an import. Shared runtime/caches are not part of this source package.

See `GATE_PROPOSAL.json` for the proposed bounded, single-root review/check. Source review and a separate compiler release are required.

## Remaining selected obligations

The lookup and phase labels are not decoded from JSON here. All ordinary endpoint adapters and residual wrappers need their own exact recipes and coverage; none may be silently omitted from a full stream.

PR516 full-state endpoint reuse separately requires the actual physical execution equality, owner injection, complete scalar helper rows and off-diagonal helper columns, and chart/operator identification. Coefficient/tableau work expansion and its complete state domain are still separate from the local macro stream. No cleanup, physical cost, or end-to-end construction claim is supplied.
