# Additional A5 blocks with balanced semantic composition

This is an incremental contribution on [PR #27](https://github.com/CrocSwap/integer-mult-bounds/pull/27),
pinned at c297233e788a23e9833ad1ee07fc8517accd0f42. The new geometry, finite moment and conditional assembly have separate independent reviews. The resulting conditional witness is

$$
\kappa=\frac{1202652036}{10^{14}}=1.202652036\times10^{-5},\qquad
T(n)=O\!\left(n(\log n)^{1-\kappa}\right).
$$

Relative to PR27's $119720853/10^{13}$, the gain is $5443506/10^{14}$,
about 0.455%. This is an asymptotic exponent improvement, not a practical speedup.
This is a fixed-network contribution complementary to newer rectangular-dimension
proposals such as PR28; it makes no current-record claim.

The new A5 profile replaces 61 singleton children plus width838 with eleven
singletons plus widths28,22,838 in each of 2N occurrences. Its exact bit saving
is $2405333/200000000000$. It leaves the PR24 graph, frame schedule, total rank,
wire count and largest child unchanged. The composition retains PR21's complex
saving $18/10^6$, the PR23 semantic guard and PR27's product row stock $p^{86000}$.
The balanced layout is inherited from the explicitly cited RaD arguments.

- [Geometric proof](GEOMETRY_PROOF.md)
- [Exact moment argument](MOMENT_PROOF.md)
- [Complete conditional composition](COMPOSITION_PROOF.md)
- [Exact certificate](CERTIFICATE.json)
- [Independent review scope](REVIEW.md)
- [Source and publication hashes](SOURCE_MANIFEST.json)

## Reproduction

From this directory in a scratch copy:

    python3 explore_corners.py
    python3 check_geometry.py
    python3 check_rank_certificates.py
    python3 check_moment_independent.py
    python3 check_composition.py
    python3 check_final_assembly.py --source-root ../..

These standard-library exact controls execute no imported predecessor program.
They read pinned JSON certificates already present in the PR27 base and recreate
local mathematical control outputs. Review the scope and hypotheses in the proof;
passing finite controls alone does not establish the all-size theorem.
Publication checked hashes, syntax and paths without rerunning scientific jobs.

## Dependencies and attribution

Credit icekylinx for the PR18/24 prescribed bases and scalar producers; Rohan Arun
for PR25's first A5-block observation; Zhihao Chen (jacklightChen) for PR21/23 frames,
complex supplier and semantic compatibility; RaD/hipotures for the balanced,
routing, semantic, phase-cell inverse and bulk mechanisms; and Dominik Scholz
for the immediate PR27 composition and product-stock accounting. Their recorded
AI assistance, earlier contributors, Apache-2.0 and CC0 notices remain intact.
This new block argument and explicit composition were prepared with OpenAI
assistance. No inherited construction is presented as newly invented here.
