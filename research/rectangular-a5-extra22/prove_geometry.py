from pathlib import Path
import json,importlib.util,time
BASE=Path(__file__).parent
sp=importlib.util.spec_from_file_location('own_reviewed_rank_cuts',BASE/'helpers/rank_cuts.py');rc=importlib.util.module_from_spec(sp);sp.loader.exec_module(rc)
sp=importlib.util.spec_from_file_location('own_reviewed_corners',BASE/'helpers/explore_corners.py');em=importlib.util.module_from_spec(sp);sp.loader.exec_module(em)
a,b=28,27;n=a+b-1;I=list(range(a));R=I+[0]+I+I;C=I+I+[0]+I
rows=[(R[i],i%b) for i in range(n)];cols=[(C[-n+j],j%b) for j in range(n)]
start=time.time();witnesses=[em.elim(em.corner(a,b,R,C,seed)) for seed in (1,2,3,7)];piv=witnesses[0]['pivots'];assert all(w['pivots']==piv for w in witnesses)
cert=[]
for i,j in piv:
 x=rc.cut(a,b,rows[:i+1],cols[j+1:]);bound=sum(pj>j for pi,pj in piv[:i]);assert x['rank_bound']==bound
 cert.append(dict(row=i,pivot_column=j,expected_bound=bound,**x))
(BASE/'GEOMETRY_CERTIFICATE.json').write_text(json.dumps({'seconds':time.time()-start,'a':a,'b':b,'row_edges':rows,'column_edges':cols,'witnesses':witnesses,'rank_cuts':cert},indent=2)+'\n')
for x in cert:
 if 30<=x['row']<=51:print(x['row'],x['pivot_column'],x['rank_B_S'],x['rank_C_complement'],'L',[s for s in x['S'] if s<a],'R',[s-a for s in x['S'] if a<=s<a+b],'*',a+b in x['S'])
