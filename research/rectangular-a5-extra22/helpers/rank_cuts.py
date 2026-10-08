"""Independent symbolic rank certificates using bipartite forest incidence."""
from collections import deque
from functools import lru_cache
import json,time
from pathlib import Path
BASE=Path(__file__).parent

def specs():
    return [(25,23,list(range(25))+list(range(7))+list(range(25))*2,list(range(25))*2+list(range(7))+list(range(25)),'PR25'),(32,30,list(range(32))+list(range(1,32))+[0],[31]+list(range(31))+list(range(32)),'PR24')]

def forest_rank(a,b,edges):
    d=a+b; par=list(range(d))
    def find(x):
        while x!=par[x]:x=par[x]
        return x
    for u,v in edges:
        u0,v0=find(u),find(a+v)
        assert u0!=v0,'Not a forest'
        par[u0]=v0
    comps={}
    for v in range(d):comps.setdefault(find(v),[]).append(v)
    comps=[(sum(1<<v for v in vs),sum(1<<v for v in vs if v<a),sum(1<<v for v in vs if v>=a),len(vs)) for vs in comps.values() if len(vs)>1]
    @lru_cache(None)
    def rank(mask):
        r=0;constant_dependent=True
        for comp,ls,rs,size in comps:
            r+=min((mask&comp).bit_count(),size-1)
            if mask&ls!=ls and mask&rs!=rs:constant_dependent=False
        if mask&(1<<d) and not constant_dependent:r+=1
        return r
    return rank

def cut(a,b,edges1,edges2):
    r1=forest_rank(a,b,edges1);r2=forest_rank(a,b,edges2)
    d=a+b+1;E=(1<<d)-1;I=0
    while True:
        size=I.bit_count();ins=[f for f in range(d) if I>>f&1];outs=[e for e in range(d) if not I>>e&1]
        reached={e:None for e in outs if r1(I|1<<e)==size+1};q=deque(reached);end=None
        while q and end is None:
            v=q.popleft()
            if not I>>v&1:
                if r2(I|1<<v)==size+1:end=v;break
                ns=[f for f in ins if r2((I^(1<<f))|1<<v)==size]
            else:
                ns=[e for e in outs if r1((I^(1<<v))|1<<e)==size]
            for z in ns:
                if z not in reached:reached[z]=v;q.append(z)
        if end is None:
            R=sum(1<<z for z in reached);S=E^R
            val=r1(S)+r2(R)
            assert val==size
            return {'S':[z for z in range(d) if S>>z&1], 'rank_B_S':r1(S),'rank_C_complement':r2(R),'rank_bound':val,'common_independent_set':[z for z in range(d) if I>>z&1]}
        v=end
        while v is not None:I^=1<<v;v=reached[v]
        assert r1(I)==r2(I)==I.bit_count()

def main():
    runs=json.loads((BASE/'corner_runs.json').read_text());out={};start=time.time()
    for a,b,R,C,name in specs():
        n=a+b-1;C=C[-n:];rows=[(R[i],i%b) for i in range(n)];cols=[(C[j],(a*b-n+j)%b) for j in range(n)]
        piv=runs['cases'][name][0]['pivots'];cert=[]
        for i,j in piv:
            x=cut(a,b,rows[:i+1],cols[j+1:]);expected=sum(pj>j for pi,pj in piv[:i]);
            assert x['rank_bound']==expected,(name,i,j,x['rank_bound'],expected)
            cert.append(dict(row=i,pivot_column=j,expected_bound=expected,**x))
        out[name]={'a':a,'b':b,'row_edges':rows,'column_edges':cols,'certificates':cert}
        print(name,'done',time.time()-start,flush=True)
    (BASE/'symbolic_rank_cuts.json').write_text(json.dumps({'seconds':time.time()-start,'cases':out},indent=2)+'\n')
if __name__=='__main__':main()
