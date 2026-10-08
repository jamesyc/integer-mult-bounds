#!/usr/bin/env python3
"""Original exact checker: proposed PR24 A5 regrouping + attributed balanced transfer.
Does not import or execute any supplier code. Supplier identities remain hypotheses.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import comb
import hashlib,json,time,argparse
HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-root',type=Path,help='Root of the inherited PR27 repository; omit for the local research cache.')
parser.add_argument('--output',type=Path,default=HERE/'BALANCED_CHECKS.json')
args=parser.parse_args()
CACHE=HERE.parent if (HERE.parent/'pr24').is_dir() and args.source_root is None else None
ROOT=(args.source_root or HERE.parents[1]).resolve()
PATHS={
 'certificates/endpoint-gauge-network.json':'pr24/certificates/endpoint-gauge-network.json',
 'research/translated-partial/complex-certificate.json':'pr21/research/translated-partial/complex-certificate.json',
 'notes/semantic-bulk-17-note.tex':'pr23/notes/semantic-bulk-17-note.tex',
 'notes/endpoint-semantic-composition.tex':'pr27/notes/endpoint-semantic-composition.tex',
 'certificates/endpoint-semantic-composition.json':'pr27/certificates/endpoint-semantic-composition.json',
 'references/rad20/SOURCE.json':'pr23/references/rad20/SOURCE.json'}
def source(name):
 if CACHE is None:return ROOT/name
 return CACHE/(PATHS.get(name,'pr23/'+name))
started=time.monotonic()
def ceil(x): return -(-x.numerator//x.denominator)
def ser(x):
 if isinstance(x,Q): return str(x)
 if isinstance(x,dict): return {str(k):ser(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)): return [ser(v) for v in x]
 return x

def log_upper(x):
 k=0
 while x>2: x/=2; k+=1
 def short(y):
  z=(y-1)/(y+1)
  return 2*sum((z**(2*j+1)/Q(2*j+1) for j in range(24)),Q(0))+2*z**49/(49*(1-z*z))
 return Q(ceil(10**12*(short(x)+k*short(Q(2)))),10**12)

def moment(hist,m,W,a,quadratic):
 out=Q(0);logs={}
 for t,n in sorted(hist.items()):
  assert 0<t<m and n>0
  logs[t]=ell=log_upper(Q(m,t));u=a*ell
  assert 0<=u<1
  enclosure=1+u+u*u/(2*(1-u/3)) if quadratic else 1/(1-u)
  out+=Q(n*t,m*W)*enclosure
 return out,logs

net=json.loads(source('certificates/endpoint-gauge-network.json').read_text())
cc=json.loads(source('research/translated-partial/complex-certificate.json').read_text())
old=net['bit']; cnt=old['counts'];mb,Wb,sb,N=cnt['m'],cnt['W'],cnt['total_rank'],cnt['N']
hist=dict(old['child_width_multiplicities'])
old_mass=sum(t*n for t,n in hist.items()); assert old_mass==sb
baseline_moment,_=moment(hist,mb,Wb,Q(old['saving']),True)
assert baseline_moment==Q(old['moment_upper'])<1
# Exactly2N A5 residuals change their contiguous block partition, not their rank.
hist[1]-=50*(2*N)
hist[28]=hist.get(28,0)+2*N
hist[22]=hist.get(22,0)+2*N
assert sum(t*n for t,n in hist.items())==sb
assert max(hist)==38340
new_a=Q(2405333,200000000000)
bit_moment,bit_logs=moment(hist,mb,Wb,new_a,True)
assert bit_moment<1

mc,Wc,sc=cc['m'],cc['W'],cc['s']; b=Q(cc['a_c'])
ch={int(t):int(n) for t,n in cc['child_counts'].items()}
assert sum(t*n for t,n in ch.items())==sc
phase_moment,phase_logs=moment(ch,mc,Wc,b,False)
assert phase_moment<1
rc=max(ch);rb=max(hist)
Gates=3*comb(28,3)**2*(4*64298+4*comb(28,3)+4)
E=64*(Wc+mc+1)**3;literal=2*Gates*Wc*Wc+8*sc+4*Wc+4+32*mc
assert literal<E
B=sc+E;C0=32*mc*B*B
assert 2*B*(mc-rc)>=sc+E and C0>2*B+18

def halving(m,r):
 k=1
 while m**k<=2*r**k:k+=1
 assert m**(k-1)<=2*r**(k-1)
 return k
hb,hc=halving(mb,rb),halving(mc,rc)
wb,wc=Wb.bit_length(),Wc.bit_length()
coeff=wb*hb+wc*hc;degree=86000
assert (hb,hc,wb,wc)==(444,544,44,41)
assert degree>coeff*Q(51,25)

def assembly(a,kappa):
 h=Q(1,10**12);beta=Q(1,4);tau,sigma=1-a,1-b
 q=a*(1-2*h);c=q+h/4;eps=(1-h)/(1+q)
 lp=1-q;lam=(tau+lp)/2;gain=eps*q;r=(gain+1-eps)/2;delta=h/8
 internal=tau+(1-beta)*max(sigma-tau,Q(0));leaf=sigma+beta*(1-sigma)
 margins=[1-eps,a,gain,a,min(1-eps-delta,r-delta),1-eps-delta,eps]
 slacks=dict(a_positive=a,b_above_a=b-a,b_small=Q(1,32)-b,beta_positive=beta,beta_small=1-beta,
  phase_leaf_above_bit=(1-beta)*b-a,q_positive=q,q_below_internal=1-internal-q,q_below_leaf=1-leaf-q,
  c_positive=c,c_small=1-c,c_above_q=c-q,lambda_above_tau=lam-tau,lambda_above_sigma=lam-sigma,
  lambda_above_internal=lam-internal,lambda_prime_above_lambda=lp-lam,lambda_prime_below_one=q,
  compact_leaf=lp-leaf,compact_reservations=lp-(1-c),epsilon_positive=eps,epsilon_below_one=1-eps,
  semantic_guard=1-eps,K_geometry=1-eps*(1+c),K_dominates_log=eps*c,record_suffix=1-eps,
  gaussian_local=1-eps-delta,gaussian_boundary=r-delta,gamma=1-eps-r,phase_cell=eps-(1-r)/2,
  prime_packing=1-eps,alpha_positive=r,alpha_below_one=1-r,alpha_below_quarter=Q(1,4)-r,
  delta_positive=delta,delta_small=Q(1,8)-delta,short_record_fallback=eps-a,
  small_field_exposure=1-eps-gain,artificial_boundary=8-eps+r-delta-gain,
  literal_scalar_guard=Q(E-literal),row_stock_degree=degree-coeff*Q(51,25))
 slacks.update({f'margin_{i+1}_above_kappa':v-kappa for i,v in enumerate(margins)})
 assert len(slacks)==47 and all(v>0 for v in slacks.values()),{k:str(v) for k,v in slacks.items() if v<=0}
 assert min(margins)==gain
 assert 1-eps-gain==h and 1-eps-r==h/2 and 1-eps*(1+c)==h-eps*h/4
 assert 1-eps*(1+c)<kappa # Meaningful failure of the original-prefix charge.
 negatives=dict(old_prefix_fails=1-eps*(1+c)<kappa,old_guard_fails=1-eps*Q(19991,10000)<0,
  separate_exposure_fails=a*(1-eps)<kappa,unattainable_declared_bit_ceiling=a< Q(1,2**16))
 ka,km,kb=ceil(1/r),ceil(1/(eps*c)),ceil(1/(1-eps));ks=ceil(1/(eps*beta))
 cuts=dict(guard=ceil(Q((2*C0).bit_length())/(1-eps)),gamma=ceil(7/(1-eps-r)),
  alpha=16*ka*ka+1,compact=64*km*km+1,K_geometry=ceil(3/(1-eps*(1+c))),
  phase_cell=ceil(9/(eps-(1-r)/2)),period=128*kb*kb+1,leaf=ks*(4*max(mb,mc)).bit_length(),
  reservoirs=14,log_p=25)
 common=max(cuts.values())
 checks=[]
 for j in range(6):
  z=common*2**j
  tests=dict(alpha=(z//ka,8*z+64),compact=(z//km,32*z+192),period=(z//kb,16*z+56),
   rows=(z//kb,4*degree*(z+8)),leaf=(z//ks,4*max(mb,mc)))
  assert all(lhs>=rhs.bit_length() for lhs,rhs in tests.values())
  checks.append(dict(log2_input=z,tests={k:dict(power=v[0],rhs=v[1],rhs_bits=v[1].bit_length()) for k,v in tests.items()}))
 assert common>=max(2*ka,2*km,2*kb,25)
 return dict(parameters=dict(a=a,b=b,h=h,beta=beta,q=q,c=c,epsilon=eps,lambda_=lam,lambda_prime=lp,r=r,delta=delta,kappa=kappa),
  slacks=slacks,margins=margins,minimum=gain,absorption_gap=gain-kappa,scoped_limit=a/(1+a),
  cutoff_log2_input=cuts,common_cutoff=common,power_checks=checks,negative_controls=negatives)

baseline=assembly(Q(old['saving']),Q(1197222866,10**14))
combined=assembly(new_a,Q(1202652036,10**14))
prior=Q(119720853,10**13)
assert combined['parameters']['kappa']>baseline['parameters']['kappa']>prior

# Exact structural controls for supplied common groups and unchanged named slots.
partition_count=0
for n in range(1,101):
 for K in range(1,n+1):
  q=n//K; L,t=divmod(n,q); widths=[L+1]*t+[L]*(q-t)
  assert sum(widths)==n and all(K<=w<2*K for w in widths)
  for flags in [(0,0),(0,1),(1,0),(1,1)]:
   axes=[[(i,h) for h in range(n+flags[i]-1,-1,-1)] for i in range(2)]
   oldslots=axes[0]+axes[1]
   prefix=[(i,n) for i in range(2) if flags[i]]
   levels=list(range(n-1,-1,-1));off=0;newslots=prefix[:]
   for width in widths:
    for i in range(2):newslots += [(i,h) for h in levels[off:off+width]]
    off+=width
   assert len(newslots)==len(oldslots) and set(newslots)==set(oldslots)
   inverse=[newslots.index(slot) for slot in oldslots]
   assert [newslots[i] for i in inverse]==oldslots
  partition_count+=1

source_names=list(PATHS)
report_names=['bulk-resampling-tape-transfer.md','compact-arbitrary-source-routing.md',
 'downstream-microbox-resampling.md','downstream-phase-cell-inverse.md',
 'downstream-semantic-child-guard.md','review-arbitrary-routing.md',
 'review-bulk-resampling.md','review-phase-cell-inverse.md','review-semantic-child-guard.md',
 'review-balanced-transform.md','downstream-semantic-bulk-assembly.md']
rad_pin=json.loads(source('references/rad20/SOURCE.json').read_text())
assert rad_pin['commit']=='45d9b60355872041f9275f77c057514def0d45bc'
for name in report_names:
 assert hashlib.sha256(source('references/rad20/reports/'+name).read_bytes()).hexdigest()==rad_pin['source_sha256']['reports/'+name]
source_names += sorted('references/rad20/reports/'+name for name in report_names)
source_hashes={name:hashlib.sha256(source(name).read_bytes()).hexdigest() for name in source_names}

result=dict(status='AUTHOR CONDITIONAL GEOMETRY+BALANCED COMPOSITION; INDEPENDENT REVIEW REQUIRED',
 bit=dict(a=new_a,m=mb,W=Wb,s=sb,maxchild=rb,histogram=sorted(hist.items()),moment_upper=bit_moment,strict_gap=1-bit_moment,logarithm_upper=bit_logs,
  modification='2N copies: 61 singleton+838 ->11 singleton+28+22+838; actual common-basis pivot lemma supplied separately'),
 complex=dict(a=b,m=mc,W=Wc,s=sc,maxchild=rc,moment_upper=phase_moment,strict_gap=1-phase_moment,logarithm_upper=phase_logs),
 semantic=dict(grouped_scalar_upper=Gates,E=E,literal_charge=literal,strict_gap=E-literal,C0=C0,C1=1),
 product_rows=dict(bit_halving=hb,complex_halving=hc,bit_wire_bits=wb,complex_wire_bits=wc,coefficient=coeff,degree=degree,suffix_slope=4*degree),
 balanced_baseline=baseline,balanced_geometry=combined,PR27_kappa=prior,
 gain_over_PR27=combined['parameters']['kappa']-prior,ratio_over_PR27=combined['parameters']['kappa']/prior,
 named_slot_controls=dict(partitions=partition_count,long_short_shapes=4*partition_count),source_sha256=source_hashes,
 remaining_hypotheses=['Actual same-common-basis width28+22 pivot lemma and PR24 physical histogram ownership.',
 'Imported finite producer/carrier/dirty-restoration identities, and upstream finite-tape machine theorem.',
 'Pinned RaD semantic/router/balanced/phase-cell/bulk all-size proofs.',
 'BHP threshold; fixed basis/prime/native setup; catalogue domination; strict logarithmic absorption; exact recovery threshold.'])
args.output.write_text(json.dumps(ser(result),sort_keys=True,indent=2)+'\n')
print('PASS: independently rebuilt modified bit/unchanged phase moments;47 strict inequalities for each balanced row; six power-check checkpoints each.')
print('Combined kappa=',combined['parameters']['kappa'],'gap=',float(combined['absorption_gap']),'PR27 improvement=',float(result['gain_over_PR27']))
print('Bit moment gap=',float(1-bit_moment),'phase gap=',float(1-phase_moment),'common log2 input cutoff=',combined['common_cutoff'])
print('Partition/slot fixtures=',partition_count,'/',4*partition_count,'elapsed seconds=',time.monotonic()-started)
