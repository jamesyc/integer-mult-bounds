# Reused normalized-corner and incidence-rank lemma

The historical scientific source below supplies the normalized-corner,
incidence-rank and common-basis arguments reused in the rectangular proof.
Its PR24/PR25 examples are separate from the new PR28 width22 result. Their
complete earlier controls remain in the [previous scientific package](https://github.com/jamesyc/integer-mult-bounds/tree/a2d8ac18b2c5a6ca53efa802f48e64b8140ae2d9/research/a5-blocks-28-22).

# Further contiguous A5 blocks in the fixed PR18 and PR24 bases

Author-paper candidate, independently reviewed status not yet asserted. Prepared with OpenAI assistance. Builds on icekylinx PR18/24 controlled bases and producers, Rohan Arun PR25's width21 observation, Zhihao Chen PR21/23 frames and semantic composition, and RaD/hipotures PR20 analytic/tape arguments. All inherited assumptions remain explicit.

Sources: PR18 f2ab41aebad47861caf6316282c1793e5513845e, PR24 ed90fd940279c336ebc45968631bdebfb087b505, PR25 61f81dc9c864d921adbc2ddeeeec3e672e688335, with original and published hashes in SOURCE_MANIFEST.json. Relevant proof files are notes/partial-swap-basis.tex, notes/endpoint-gauge-basis.tex, and research/a5-semantic/a5-block.tex respectively. No source executable was run.

## Statement

Within the unchanged prescribed common-basis family:

- PR18/25 A5 admits 21 singleton children and blocks 5,21,481. Relative to PR25 this replaces five singleton children by one width5 child, per occurrence.
- PR24 A5 admits 11 singleton children and blocks 22,28,838. Relative to PR24 this replaces 50 singleton children by two contiguous children, per occurrence.

These are genuine increasing contiguous pivot blocks, without gathering or reversal. Both families have 2N occurrences. Their graph, producer counts, rank mass, total dimension, largest recursive child, physical frame schedule, and auxiliary endpoint identities are unchanged.

## Normalized corner and universal rank bound

Let a,b be the two inner dimensions, n=a+b−1, H=ab. With the prescribed initial row labels r_i, terminal inverse-column labels c_j, beta_i=i mod b and b_j=(H−n+j) mod b, the null corner is

Q_ij = [beta_i=b_j] p_(r_i) xi_(c_j) + [r_i=c_j] v_(beta_i) nu_(b_j) − p_(r_i) xi_(c_j) v_(beta_i) nu_(b_j).

Here xi p=nu v=1. This is PR25's formula; the same direct controlled-basis calculation applies to the PR24 label prescriptions. All used line coordinates can be assumed nonzero. Divide row i by p_(r_i)v_(beta_i), and column j by xi_(c_j)nu_(b_j). The resulting matrix is

A_ij = [r_i=c_j] x_(r_i) + [beta_i=b_j] y_(beta_i) −1,

where x_r=1/(p_r xi_r), y_s=1/(v_s nu_s). Define fixed integer matrices B_i=(e_(r_i),e_(beta_i),1) and C_j=(e_(c_j),e_(b_j),1). Then A=B diag(x,y,−1) C^t.

For any latent-coordinate subset S, any initial row interval U and terminal column interval V,

rank A_(U,V) ≤ rank B_(U,S) + rank C_(V,S-complement).    (1)

This follows by splitting the diagonal sum into S and its complement, applying subadditivity, and bounding each product rank by one of its factors. It is valid for every specialization, so the resulting zeros are identities, not numerical conjectures.

## Exact incidence-rank rule

Ignoring the last constant coordinate, B or C is the unoriented edge-vertex incidence matrix of a bipartite forest. Its selected-vertex-column rank is

sum over nontrivial connected components T of min(number of selected vertices in T, |T|−1).

Proof: signing all right-side columns converts it to oriented incidence. A tree has exactly the one full-support column dependence, so any proper subset is independent. Different components have disjoint row support. If the constant column is selected, it increases rank by one precisely when some component contains an unselected vertex on both sides. Indeed a linear combination of selected vertex columns equals the constant vector exactly when each component admits values z_left=t, z_right=1−t with z=0 on every unselected vertex. Such t exists exactly when the component has no unselected left vertex or no unselected right vertex. This proves the rule without trusting any search algorithm.

## Complete pivot permutations and upper-rank cuts

All indices are zero-based; [u,v] means an inclusive integer interval and can be empty. A rightmost-pivot lower/lower elimination has the following generic permutations.

PR25 (a,b)=(25,23), n=47:
- pi(0)=46
- pi(i)=i+24 for 1≤i≤21
- pi(i)=46−i for 22≤i≤32
- pi(i)=i−24 for 33≤i≤37
- pi(i)=46−i for 38≤i≤46

PR24 (a,b)=(32,30), n=61:
- pi(0)=60
- pi(i)=i+31 for 1≤i≤28
- pi(i)=60−i for 29≤i≤34
- pi(i)=i−31 for 35≤i≤56
- pi(i)=60−i for 57≤i≤60

For each i put U=[0,i], V=[pi(i)+1,n−1]. The desired upper bound is r_i=number of k<i with pi(k)>pi(i). Outside the increasing runs, this bound follows directly from the number of columns in V (or V empty). On the first increasing run in either case choose S containing *, all left vertices greater than i, and all right vertices greater than i. Its ranks in (1) are 1 and 0, yielding r_i=1.

For PR25's second run let i=33+t, pi(i)=9+t, 0≤t≤4. Take
- S_left=[0,6] union [11+t,24]
- S_right=[0,4] union [9+t,22]
- * in S.
The incidence rule gives ranks 29−t and 4+t in (1), summing to 33, which is exactly r_i.

For PR24's second run let i=35+t, pi(i)=4+t, 0≤t≤21. Take
- S_left=[0,2] union [6+t,31]
- S_right={0} union [4+t,29]
- * in S.
The incidence rule gives ranks 32−t and 3+t in (1), summing to 35, exactly r_i.

The full fixed row/column edge lists and all 108 cuts are in symbolic_rank_cuts.json. The compact interval formulas above, together with the elementary incidence-rank rule, are the proof of all uniform upper-rank bounds. The matroid-intersection search in rank_cuts.py merely discovered these cuts and is not a proof dependency.

## Nonvanishing on the actual normalized projector family

To supply the opposite inequalities, use the explicit rational specialization, for seed s=1:

p_r=1+((r+s)7 mod19), raw_xi_r=1+((r+s)11 mod23), xi_r=raw_xi_r/(sum_q p_q raw_xi_q);
v_j=1+((j+s)13 mod29), raw_nu_j=1+((j+s)17 mod31), nu_j=raw_nu_j/(sum_k v_k raw_nu_k).

Every coordinate is positive and xi p=nu v=1. Exact rational elimination yields the stated pivot permutations. In particular every square minor in initial rows [0,i] and columns {pi(0),...,pi(i)} is nonzero. These minor assertions are a finite rational certificate, independently reproducible using explore_corners.py; seeds2,3,7 are redundant controls. The four records are in corner_runs.json. A rational nonzero witness is sufficient to prove a minor is not the zero rational function, unlike using samples to assert an identity.

For completeness, at the first row where a proposed pivot could differ, (1) forbids any nonzero residual to the right of pi(i); the nonzero initial-row minor forces the residual at pi(i) to be nonzero. Induction therefore establishes the permutation on the nonempty open set where these minors are nonzero.

Every rank-one pair (p,xi) with xi p=1 lies in the GL_a similarity orbit of each fixed rank-one projector, and similarly for (v,nu). Hence the witness is in the free L_a,L_b parameter space of the prescribed basis. The nonzero conditions can be multiplied with all inherited minors on its nonempty irreducible completion family. This preserves simultaneous availability for the finitely many producer projectors; it does not require the displayed specialization itself to satisfy all inherited minors.

## Physical block and moment consequence

The unchanged outer rank-one factor gives only nonzero diagonal scalings. The actual projector corner is −Q. Neither changes the pivot permutation. The inherited large-projector identity supplies the unchanged middle identity, width481 or838. The inherited exact lower-triangular partial-swap conjugation converts each increasing contiguous run into one recursive interchange.

For exponent tau=1−a_b in (0,1), replacing t singleton children by a width-t child changes the moment numerator by t^tau−t<0. Thus each stated block strictly improves the bit characteristic at the previously certified saving. Quantitative exact revised moments are provided separately, and no final exponent is asserted until the compatible assembly and independent review pass.

## Scope and limitation

This is a paper proof plus finite rational nonvanishing certificates, not Lean or an unconditional multiplication theorem. The fixed alphabet, fixed number of one-dimensional tapes, analytic, row-stock, routing, bulk, precision, prime-packing and constructive-preparation hypotheses remain inherited. No schedule improvements are added twice: PR21's translated auxiliary endpoint and PR24's gauge implement the same algebraic operation in different graphs. The new result changes only the A5 child profile within each graph.
