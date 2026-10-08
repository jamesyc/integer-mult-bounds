#!/usr/bin/env python3
"""Reviewer-owned rational checks. No author executable is imported or run.
Budget: expected <2 seconds and <64 MiB, externally capped at 60 seconds.
"""
from fractions import Fraction as Q
from pathlib import Path
from hashlib import sha256
from math import factorial
import json
import time

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[1]
start=time.monotonic()
author=json.loads((HERE/'EXACT_MOMENTS.json').read_text())

def logs(ratio):
    power=0
    while ratio>2:
        ratio/=2;power+=1
    def series(x):
        z=(x-1)/(x+1)
        low=2*sum((z**(2*j+1)/(2*j+1) for j in range(32)),Q(0))
        return low,low+2*z**65/(65*(1-z*z))
    l,u=series(ratio);l2,u2=series(Q(2))
    l+=power*l2;u+=power*u2
    scale=10**15
    l*=scale;u*=scale
    return Q(l.numerator//l.denominator,scale),Q(-(-u.numerator//u.denominator),scale)

results=[]
for row in author['cases']:
    if row['name']!='PR24_width28_width22':continue
    source_path=PROJECT/'certificates/endpoint-gauge-network.json'
    raw=source_path.read_bytes()
    assert sha256(raw).hexdigest()==row['input_sha256']
    source=json.loads(raw)['bit']
    old=dict(source['child_width_multiplicities'])
    expected=dict(old)
    copies=2*row['N']
    for width in row['new_A5_blocks']:
        expected[1]-=copies*width
        expected[width]=expected.get(width,0)+copies
    assert sorted(expected.items())==[tuple(x) for x in row['child_width_multiplicities']]
    m,W=row['m'],row['W']
    s=sum(r*n for r,n in expected.items())
    assert s==sum(r*n for r,n in old.items())
    assert W*m-s==row['deficit']
    assert all(0<r<m and n>0 for r,n in expected.items())
    assert max(expected)==row['max_child']
    a=Q(row['saving'])
    interval={r:logs(Q(m,r)) for r in expected}
    for r,(lo,hi) in interval.items():
        assert hi<=Q(row['logarithm_upper_bounds'][str(r)])
        assert lo>0
    # Reconstruct the author's stated upper certificate only after proving logs.
    claimed_upper=Q(0)
    independent_upper=Q(0)
    for r,n in expected.items():
        u=a*Q(row['logarithm_upper_bounds'][str(r)])
        assert 0<u<3
        claimed_upper+=Q(n*r,W*m)*(1+u+u*u/(2*(1-u/3)))
        u=a*interval[r][1]
        assert 0<u<8
        # Terms through degree six, with geometric upper tail from term seven.
        expupper=sum((u**j/factorial(j) for j in range(7)),Q(0))+u**7/(factorial(7)*(1-u/8))
        independent_upper+=Q(n*r,W*m)*expupper
    assert 1-claimed_upper==Q(row['moment_gap'])>0
    assert independent_upper<1
    def lower(hist,saving):
        ans=Q(0)
        for r,n in hist.items():
            u=saving*interval[r][0]
            ans+=Q(n*r,W*m)*sum((u**j/factorial(j) for j in range(5)),Q(0))
        return ans
    next_lower=lower(expected,a+Q(1,10**12))
    old_lower=lower(old,a)
    assert next_lower>1 and old_lower>1
    assert Q(row['next_grid_actual_excess_lower'])>0 and Q(row['old_profile_actual_excess_lower'])>0
    results.append({'name':row['name'],'saving':str(a),'rank_mass':s,'max_child':max(expected),'claimed_gap_exactly_reconstructed':str(1-claimed_upper),'independent_upper_gap':str(1-independent_upper),'next_grid_actual_excess_lower':str(next_lower-1),'old_actual_excess_lower':str(old_lower-1),'input_sha256':row['input_sha256']})
out={'status':'PASS: finite moments only; geometry and full assembly reviewed separately','reviewer_source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'cases':results,'elapsed_seconds':time.monotonic()-start}
(HERE/'MOMENT_REVIEW_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
for row in results:print(row['name'],'upper gap',float(Q(row['independent_upper_gap'])),'next-grid actual excess >=',float(Q(row['next_grid_actual_excess_lower'])))
print('PASS',len(results),'cases in',out['elapsed_seconds'],'seconds')
