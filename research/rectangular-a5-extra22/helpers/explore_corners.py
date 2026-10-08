from fractions import Fraction as F
import json,time

def corner(a,b,R,C,seed):
    n=a+b-1; H=a*b
    p=[1+((i+seed)*7%19) for i in range(a)]
    xi=[F(1+((i+seed)*11%23)) for i in range(a)]
    s=sum(x*y for x,y in zip(p,xi));xi=[x/s for x in xi]
    v=[1+((i+seed)*13%29) for i in range(b)]
    nu=[F(1+((i+seed)*17%31)) for i in range(b)]
    s=sum(x*y for x,y in zip(v,nu));nu=[x/s for x in nu]
    rows=[]
    for i in range(n):
        beta=i%b;r=R[i];row=[]
        for j in range(n):
            c=C[len(C)-n+j]; bb=(H-n+j)%b
            row.append((beta==bb)*p[r]*xi[c]+(r==c)*v[beta]*nu[bb]-p[r]*xi[c]*v[beta]*nu[bb])
        rows.append(row)
    return rows

def elim(rows):
    A=[list(r) for r in rows]; n=len(A); piv=[];left=set(range(n))
    for i in range(n):
        candidates=[j for j in left if A[i][j]]
        if not candidates:raise ValueError(('singular',i))
        j=max(candidates);left.remove(j);piv.append((i,j));p=A[i][j]
        for k in range(i+1,n):
            if A[k][j]:
                f=A[k][j]/p
                for l in left:A[k][l]-=f*A[i][l]
                A[k][j]=F(0)
    runs=[]
    for ij in piv:
        if runs and ij[0]==runs[-1][-1][0]+1 and ij[1]==runs[-1][-1][1]+1:runs[-1].append(ij)
        else:runs.append([ij])
    return {'pivots':piv,'runs':runs,'widths':[len(x) for x in runs]}

def main():
    cases={};t=time.time()
    for a,b,R,C,name in [(25,23,list(range(25))+list(range(7))+list(range(25))*2,list(range(25))*2+list(range(7))+list(range(25)),'PR25'),(32,30,list(range(32))+list(range(1,32))+[0],[31]+list(range(31))+list(range(32)),'PR24')]:
        cases[name]=[elim(corner(a,b,R,C,seed)) for seed in [1,2,3,7]]
    print(json.dumps({'seconds':time.time()-t,'cases':cases},indent=2))
if __name__=='__main__':main()
