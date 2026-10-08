from fractions import Fraction as F
from pathlib import Path
import hashlib,json,time
HERE=Path(__file__).resolve().parent

def labels(a,b,which):
    n=a+b-1
    if which=='PR24':
        R=list(range(a))+list(range(1,a))+[0]
        C=[a-1]+list(range(a-1))+list(range(a))
    else:
        R=list(range(a))+list(range(7))+list(range(a))*2
        C=list(range(a))*2+list(range(7))+list(range(a))
    return [(R[i],i%b) for i in range(n)],[(c,(a*b-n+j)%b) for j,c in enumerate(C[-n:])]

def right_pivots(M):
    A=[list(r) for r in M]; available=set(range(len(A)))
    piv=[];values=[];diag=[]
    for row in range(len(A)):
        col=max(j for j in available if A[row][j])
        value=A[row][col]
        piv.append(col);values.append(str(value));available.remove(col)
        # Store the row's exact active entries before further elimination.
        diag.append({str(j):str(A[row][j]) for j in sorted(available|{col}) if A[row][j]})
        for other in range(row+1,len(A)):
            coeff=A[other][col]/value
            if coeff:
                for j in available:A[other][j]-=coeff*A[row][j]
                A[other][col]=F(0)
    return piv,values,diag

def run(which,a,b,seed):
    rows,cols=labels(a,b,which); n=len(rows)
    # p=v=ones, dual vectors are positive rational vectors summing to one.
    wa=[(i+1)**seed+1 for i in range(a)]
    wb=[(2*i+1)**seed+2 for i in range(b)]
    xi=[F(w,sum(wa)) for w in wa];nu=[F(w,sum(wb)) for w in wb]
    Q=[[int(beta==bb)*xi[c]+int(r==c)*nu[bb]-xi[c]*nu[bb] for c,bb in cols] for r,beta in rows]
    # Diagonal-scale Q using positive line coordinates; derive this formula independently.
    A=[[Q[i][j]/(xi[c]*nu[bb]) for j,(c,bb) in enumerate(cols)] for i in range(n)]
    latent=[[int(r==c)/xi[r]+int(beta==bb)/nu[beta]-1 for c,bb in cols] for r,beta in rows]
    assert A==latent
    piv,values,active=right_pivots(Q)
    if which=='PR24': expected=[60]+list(range(32,60))+[31,30,29,28,27,26]+list(range(4,26))+[3,2,1,0]
    else: expected=[46]+list(range(25,46))+list(range(24,13,-1))+list(range(9,14))+list(range(8,-1,-1))
    assert piv==expected,(which,piv,expected)
    widths=[]
    for i,j in enumerate(piv):
        if i and j==piv[i-1]+1:widths[-1]+=1
        else:widths.append(1)
    # Every displayed pivot is a nonzero normalized principal-in-pivot-order minor ratio.
    determinant=F(1)
    for v in values:determinant*=F(v)
    if which=='PR24': start,end=35,57
    else:start,end=33,38
    return {'case':which,'seed':seed,'pivots':piv,'widths':widths,'pivot_values':values,
            'ordered_minor_product':str(determinant),'late_block_rows':active[start:end],
            'diagonal_scaling_identity':True,'rank':n}

def main():
    begin=time.monotonic(); result={'evidence':'Exact finite nonvanishing witnesses; symbolic rank identities reviewed separately.'}
    result['controls']=[run(case,a,b,seed) for case,a,b in [('PR24',32,30),('PR25',25,23)] for seed in [1,2]]
    result['accounting']={'PR24':{'rank_old':61+838,'rank_new':11+28+22+838,'call_reduction_per_copy':(61+1)-(11+3)},'PR25':{'rank_old':26+21+481,'rank_new':21+5+21+481,'call_reduction_per_copy':(26+2)-(21+3)}}
    result['runtime_seconds']=time.monotonic()-begin
    out=HERE/'independent_control_results.json';out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'runtime_seconds':result['runtime_seconds'],'controls':len(result['controls']),'accounting':result['accounting'],'output':str(out)}))
if __name__=='__main__':main()
