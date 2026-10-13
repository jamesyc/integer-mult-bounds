# Attribution and scope notice

BitXorConjugacy.lean is distributed under Apache-2.0. The repository's root LICENSE contains the license text (Git blob 261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64 at publication-context commit 47481c89fd30a43f8f882eb4b391e89c29273fd0).

The source was prepared with OpenAI assistance. Its motivation is Gareth Davidson (@bitplane), PR915, with mathematical head 7d5ef1dcf994d0542f2d302110b33780f5504ab7 and publication head e9daefe320a0043000bd9746664ed02c3287d056. That work credits the PR794/713/716/686 restored-basis and semantic-boundary lineage.

The ordered XOR interpreter and reversal API are the exact public PR590 and PR597 sources identified in DEPENDENCIES.json. Those source files are referenced, not duplicated here; their existing source headers, licenses and original contributor attribution remain intact. This contribution does not claim authorship of those predecessor proofs.

Prior formalization: Anthony (@anthonylei), PR774, exact head 50f8c366f27a9083e0655593a1be3d6810d1f053, research/r420-forest-cut-budget/Forest.lean (Git blob abcaac58a901cc1d97be549aa9fdf93fbc01182e), specifically TargetForest.run_add, compensated_injection and compensatedShear_correct. Those results already establish the generic algebra in a separately defined reversible unary-gate model. This contribution is an interface generalization to the published PR590/597 model, not a mechanism-priority claim.

This package proves generic XOR linearity and restored-basis conjugacy under explicit hypotheses. It does not adopt a finite D word or establish physical realization, signed-positive bounds, a hosted invoice, a new kappa value or a multiplication theorem.
