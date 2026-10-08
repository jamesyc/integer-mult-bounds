> Current status: independently accepted at the scope in [REVIEW.md](REVIEW.md). Original author/pending labels below describe the frozen submission. Imported predecessor hypotheses remain explicit.

# A second contiguous A5 block in PR28's unchanged rectangular basis

Author-paper candidate; independent review required before acceptance. This extends Rohan Arun's PR28 at rohanarun/integer-mult-bounds commit3eafe5a35b572fe38e7d64a55ce5cac1d8838bee. Preserve icekylinx's PR18 prescribed basis and partial-swap framework, Zhihao Chen's PR21/23 translated frames and semantic composition, RaD/hipotures PR20 analytic/tape transfer, PR25's first-block observation and all preceding contributor/license records. The new contribution is the late width22 block and its uniform rank-cut certificate.

## Exact scope

Retain (a,b,k)=(28,27,57), H=756, outer null-boundary size a+k=85, and the entire PR28 physical network and common-basis family. Its full inner prescriptions are R=[I,[0],I,I] and C=[I,I,[0],I], I=[0,...,27]. Their A5 nullity54 corner uses

r=[0,...,27,0,0,...,24], c=[3,...,27,0,0,...,27], beta_i=b_i=i mod27.

The common-basis and A1/A3 compatibility arguments in the pinned PR28 remain dependencies. None is changed or inferred from the numerical controls here.

The A5 profile improves from29 singleton children;25,648 to7 singleton children;25,22,648. Its rank remains702. There are2N copies, so the global child-list change is subtraction44N from width1 and addition2N to width22. No other width, physical role, graph, total rank, maximum child or endpoint frame changes.

## Universal factorization and rank lemma

Use exactly the proved normalized-corner and incidence-rank lemmas of COMMON_CORNER_LEMMA.md (SHA256 ac6601c778ab1b2fda48ca136f83379751ec488c9ef4f0e5e3b58e17ef539c68). For completeness, after nonzero row/column scalings the A5 null corner is

A_ij=[r_i=c_j]x_(r_i)+[beta_i=b_j]y_(beta_i)−1
     = (B diag(x,y,−1) C^t)_ij,

B_i=(e_(r_i),e_(beta_i),1), C_j=(e_(c_j),e_(b_j),1), x_r=1/(p_r xi_r), y_s=1/(v_s nu_s), xi p=nu v=1.

For any latent-coordinate subset S,

rank A_(U,V) ≤rank B_(U,S)+rank C_(V,S-complement). (1)

Selected vertex-column ranks in a bipartite forest are the sum over components of min(selected vertices, component size−1). Adding the constant column raises rank by one exactly when at least one component has an unselected vertex on each bipartition side. The proof is ordinary tree-incidence linear independence plus the solutions z_left=t,z_right=1−t to an edgewise constant sum. Thus every rank-cut upper bound below is a parameter-uniform identity, not extrapolation from samples.

## Pivot permutation and late-block cuts

The generic rightmost-pivot lower/lower permutation is

pi(0)=53;
pi(i)=i+27, 1≤i≤25;
pi(i)=53−i, 26≤i≤29;
pi(i)=i−28, 30≤i≤51;
pi(i)=53−i, 52≤i≤53.

For each i inspect U=[0,i] and V=[pi(i)+1,53]. Outside the two increasing runs, the required upper rank bound is merely the number of columns of V. For the first run the PR28/25 first-pivot cancellation applies; alternatively choose S consisting of *, all left labels greater than i and all right labels greater than i. The ranks in(1) are1 and0.

For the new run write i=30+t, pi(i)=2+t, 0≤t≤21. Choose

S_left={0} union [4+t,27],
S_right=[3+t,26],
and include *.

The incidence-rank rule gives

rank B_([0,30+t],S)=27−t,
rank C_([3+t,53],S-complement)=3+t.

Their sum is30. Exactly30 earlier pivots lie strictly right of2+t, hence elimination has no residual entry strictly right of the proposed pivot. The full edge lists and all54 rank-cut certificates are in GEOMETRY_CERTIFICATE.json. The interval formulas are the general proof; the search that found them is not a proof dependency.

To prove the pivots themselves nonzero, use the explicit normalized rational specialization from the earlier proof: p_r=1+7(r+s) mod19, raw_xi_r=1+11(r+s) mod23, v_j=1+13(j+s) mod29, raw_nu_j=1+17(j+s) mod31, where residues are taken before adding1. Normalize xi and nu by their respective pairings. Seed s=1 supplies exact nonzero initial-row minors; seeds2,3,7 are redundant controls. All four Fraction-only eliminations give the stated permutation. These are legitimate points in the free GL_a and GL_b rank-one similarity orbits. Their nonzero minors therefore define a nonempty open subset and can be multiplied with the unchanged finite family of inherited nonzero conditions.

Inductively, the uniform upper bounds forbid a pivot to the right of pi(i), and the nonzero initial-row minor forces the residual at pi(i) to be nonzero. Thus the permutation holds generically in the prescribed family. Its rows30 through51 and columns2 through23 are equally ordered contiguous intervals. The inherited exact lower-triangular partial-swap conjugation therefore executes them with one width22 child. The inherited middle block648 is untouched.

## Evidence and limitations

prove_geometry.py imports only our independently authored earlier exact-corner and rank-cut helpers. It executes no external repository code. GEOMETRY_CERTIFICATE.json contains four exact normalized witnesses and54 symbolic rank cuts. The original checks took under one second. The unchanged-basis result is sufficient; exploratory singleton-label variations are not needed and are excluded from this proof.

A pure regrouping of22 singleton children into one width22 child strictly decreases the bit moment at every exponent tau in(0,1), since22^tau<22. Quantitative bit and final assembly certificates are separate. This is a conditional paper result with finite rational nonvanishing certificates; it is not formal verification or an unconditional multiplication theorem. All analytic, fixed finite-alphabet/tape, precision, stock, routing, bulk, prime-packing and finite-preparation assumptions remain inherited.
