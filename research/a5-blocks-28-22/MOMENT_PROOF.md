> Current evidence: the relevant new component has independent paper/arithmetic acceptance at the scope in [REVIEW.md](REVIEW.md). Original author-status wording is historical; imported predecessor hypotheses remain explicit.

# Exact finite bit moments for the additional A5 blocks

Author-certificate, separate from the frozen geometry paper. No final multiplication exponent is asserted by this packet. The unchanged pinned input certificates and analytic/machine interfaces remain hypotheses. All inherited contributor attributions in GEOMETRY_PROOF.md apply.

## Profile changes

For PR24 let N=198959488000, W=9854325632000, m=38400. The frozen geometry paper supplies 2N copies of the new A5 profile 11 singleton children;22,28,838. From PR24's original complete child list, subtract 50(2N) from width1 and add 2N to each of widths22 and28. Every other multiplicity is unchanged. The total rank is 378405934031283200, the deficit Wm−s is170237516800, and the largest child is38340. Thus the scalar graph and all graph-derived precision and row-stock quantities are unchanged.

Exact resulting saving:

a_b=2405333/200000000000=0.000012026665.

The upper moment is strictly less than1 by more than1.6897×10^−15. The complete rational fraction and all updated multiplicities are in EXACT_MOMENTS.json, case PR24_width28_width22.

Two separate comparisons are supplied, not stacked with this result:
- PR24 width28 only: a_b=3000929/250000000000=0.000012003716, gap>1.6974×10^−14.
- PR25 additional width5 only: a_b=5725197/500000000000=0.000011450394, gap>1.4722×10^−14. PR25's previously established width21 remains in the source histogram.

## Rational enclosure

Write Psi(1−a)=sum_t c_t t/(Wm) exp(a log(m/t)). For 1≤y≤2 and z=(y−1)/(y+1), the positive atanh series gives

2 sum_(j=0)^23 z^(2j+1)/(2j+1) ≤ log y ≤ 2 sum_(j=0)^23 z^(2j+1)/(2j+1)+2z^49/[49(1−z²)].

Extract powers of2 from each m/t, apply the same formula to log2, and round the resulting upper bound upward to a multiple of10^−12. For u=a times that upper bound, check0≤u<3 and use

exp(u) ≤1+u+u²/[2(1−u/3)].

The latter follows termwise from k!≥2·3^(k−2) for k≥2. Summing positive rational terms gives the stated upper moment and strict gap. All arithmetic uses Python's standard-library Fraction; the script imports JSON data only and executes no external repository code.

For rigorous negative controls, use the corresponding lower atanh sum rounded downward to10^−12 and the positive fourth-degree Taylor polynomial1+u+u²/2+u³/6+u⁴/24. Its weighted sum is a lower bound for the actual moment. For each case the next saving grid point a+10^−12 has actual moment strictly above1; the unmodified input profile at the new saving also has actual moment strictly above1. Thus these controls reject the actual moment, not merely failure of the chosen upper enclosure.

The script searches a fixed grid only to choose a witness; the proof certificate is the single resulting rational inequality and the exact rank accounting. This is a finite characteristic result, not an optimality claim beyond the adjacent10^−12 bracket for this fixed histogram.
