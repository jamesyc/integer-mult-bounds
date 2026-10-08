from pathlib import Path
from math import gcd
from functools import reduce
import hashlib,json,time
HERE=Path(__file__).resolve().parent

def exact_rank(matrix):
    basis={}
    for initial in matrix:
        row=list(initial)
        while any(row):
            lead=next(k for k,x in enumerate(row) if x)
            if lead not in basis:
                g=reduce(gcd,row)
                if row[lead]<0:g=-g
                basis[lead]=[x//g for x in row]
                break
            known=basis[lead];a=row[lead];b=known[lead]
            row=[b*x-a*y for x,y in zip(row,known)]
            g=reduce(gcd,row)
            if g>1:row=[x//g for x in row]
    return len(basis)

def expected(which):
    if which=='PR24':
        a,b=32,30;R=list(range(32))+list(range(1,32))+[0];C=[31]+list(range(31))+list(range(32))
        P=[60]+list(range(32,60))+[31,30,29,28,27,26]+list(range(4,26))+[3,2,1,0]
    else:
        a,b=25,23;R=list(range(25))+list(range(7))+list(range(25))*2;C=list(range(25))*2+list(range(7))+list(range(25))
        P=[46]+list(range(25,46))+list(range(24,13,-1))+list(range(9,14))+list(range(8,-1,-1))
    n=a+b-1
    return a,b,[(R[i],i%b) for i in range(n)],[(c,(a*b-n+j)%b) for j,c in enumerate(C[-n:])],P

def incidence(edges,a,b,selection):
    return [[int(z==r or z==a+beta or z==a+b) for z in selection] for r,beta in edges]

def main():
    start=time.monotonic();source=HERE/'rank_cuts.json'
    raw=source.read_bytes();data=json.loads(raw);out={}
    for case in ['PR24','PR25']:
        a,b,rows,cols,P=expected(case);cert=data['cases'][case];n=len(P);universe=set(range(a+b+1))
        assert cert['row_edges']==[list(x) for x in rows]
        assert cert['column_edges']==[list(x) for x in cols]
        assert len(cert['certificates'])==n
        checks=[]
        for i,cut in enumerate(cert['certificates']):
            j=P[i];assert cut['row']==i and cut['pivot_column']==j
            S=cut['S'];assert len(set(S))==len(S) and set(S)<=universe
            other=sorted(universe-set(S))
            rb=exact_rank(incidence(rows[:i+1],a,b,S))
            rc=exact_rank(incidence(cols[j+1:],a,b,other))
            target=sum(p>j for p in P[:i])
            assert rb==cut['rank_B_S'] and rc==cut['rank_C_complement']
            assert rb+rc==cut['rank_bound']==cut['expected_bound']==target
            # Independently validate the proof's compact closed-form cuts too.
            if 1<=i<=(28 if case=='PR24' else 21):
                closed=set(range(i+1,a))|{a+z for z in range(i+1,b)}|{a+b}
            elif case=='PR24' and 35<=i<=56:
                t=i-35;closed=set(range(3))|set(range(6+t,32))|{a}|{a+z for z in range(4+t,30)}|{a+b}
            elif case=='PR25' and 33<=i<=37:
                t=i-33;closed=set(range(7))|set(range(11+t,25))|{a+z for z in range(5)}|{a+z for z in range(9+t,23)}|{a+b}
            else:closed=None
            if closed is not None:
                assert exact_rank(incidence(rows[:i+1],a,b,sorted(closed)))+exact_rank(incidence(cols[j+1:],a,b,sorted(universe-closed)))==target
            else:
                assert len(cols[j+1:])==target
            checks.append({'row':i,'pivot_column':j,'rank_B_S':rb,'rank_C_complement':rc,'rank_bound':target})
        out[case]=checks
    result={'source_sha256':hashlib.sha256(raw).hexdigest(),'rank_method':'Independent direct integer elimination, not author forest or matroid code','checks':out,'all_checks_pass':True,'runtime_seconds':time.monotonic()-start}
    (HERE/'independent_rank_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'source_sha256':result['source_sha256'],'checks':sum(map(len,out.values())),'runtime_seconds':result['runtime_seconds'],'all_checks_pass':True}))
if __name__=='__main__':main()
