# A late width22 A5 block in the fixed PR28 geometry

This increment is based on the scientific commit of
[PR #28](https://github.com/CrocSwap/integer-mult-bounds/pull/28),
3eafe5a35b572fe38e7d64a55ce5cac1d8838bee. It retains dimensions $(28,27,57)$
and has independently accepted new geometry and conditional assembly. The witness is

$$
\kappa=\frac{1228547206}{10^{14}}=1.228547206\times10^{-5},\qquad
T(n)=O\!\left(n(\log n)^{1-\kappa}\right).
$$

The sole finite-network change groups 22 additional singleton pivots into one
ordered contiguous width22 child. Each A5 occurrence has seven singleton
children plus widths25,22,648. The graph, common-basis family, W, rank sum,
physical frames and largest recursive child remain unchanged. The revised bit
saving is $12285623/10^{12}$. PR21's complex supplier remains unchanged.

The balanced semantic/bulk composition is explicitly attributed to the retained
arguments; its actual named-coordinate, precision, padding and tape interfaces
are part of the conditional proof. This is not an implementation benchmark,
whole-machine Lean theorem or claim of an unconditional/global optimum.
Other current proposals report larger exponents; this branch records the fixed-
family refinement and makes no current-record claim.

## Scientific contents

- [New geometric proof](GEOMETRY_PROOF.md)
- [Reused common-corner lemma](COMMON_CORNER_LEMMA.md)
- [Exact geometric certificate](GEOMETRY_CERTIFICATE.json)
- [Conditional balanced assembly](ASSEMBLY_PROOF.md)
- [Exact assembly certificate](ASSEMBLY_CERTIFICATE.json)
- [Review status and hypotheses](REVIEW.md)
- [Original and published hashes](SOURCE_MANIFEST.json)

## Reproduction

Use a fresh scratch copy of the inherited repository. From this directory:

    python3 -m unittest test_package.py
    python3 prove_geometry.py
    python3 check_geometry_independent.py
    python3 check_assembly.py --source-root ../..
    python3 check_assembly_independent.py --source-root ../.. --author-certificate ASSEMBLY_CERTIFICATE.json

The geometry generator imports only the two included mathematical helper
modules. The assembly checker reads pinned native JSON/text inputs and executes
no predecessor program. Generated files may include run-specific fields; compare
exact mathematical values. Publication itself runs only hash and static checks.
The included independent controls retain their accepted mathematical source; only documentary paths in the geometry checker were adapted.

## Attribution

Rohan Arun's PR28 supplies the rectangular basis, its compatibility proof and
first width25 block. icekylinx supplies the PR18 basis/partial-swap framework;
Zhihao Chen (jacklightChen) supplies PR21/23 frames and semantic compatibility;
RaD/hipotures supplies the semantic, balanced, routing, phase-cell and bulk
mechanisms. PR25 and all earlier authors, original licenses and recorded AI
assistance remain credited. The new contribution here is the late width22 block
within the unchanged family and its explicitly matched composition, prepared
with OpenAI assistance.
