#!/usr/bin/env python3
"""Original exact checker: proposed PR28 A5 regrouping + attributed balanced transfer.
Does not import or execute any supplier code. Supplier identities remain hypotheses.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import comb
from collections import Counter
import hashlib,json,time,argparse
HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-root',type=Path,help='Root of the inherited PR28 repository; omit to use a private inputs snapshot or the native two-level repository layout.')
parser.add_argument('--output',type=Path,default=HERE/'BALANCED_CHECKS.json')
args=parser.parse_args()
ROOT=(args.source_root or ((HERE/'inputs') if (HERE/'inputs').is_dir() else HERE.parents[1])).resolve()
PATHS=['research/rectangular-semantic/certificate.json', 'research/rectangular-semantic/inputs.json', 'research/rectangular-semantic/compatibility-theorem.txt', 'research/rectangular-semantic/a5-28-27-proof.txt', 'research/translated-partial/complex-certificate.json', 'notes/semantic-bulk-17-note.tex', 'references/rad20/SOURCE.json']
def source(name):return ROOT/name
EXPECTED_INPUT_SHA256={'research/rectangular-semantic/certificate.json': '95440e6e5cbdc4e9a8d4485ae2492585f1eb0a326c8f103563af562ee445cabe', 'research/rectangular-semantic/inputs.json': '3815466a9d90fcf900c68ae756660a899696bcf5ba6f6b0890bccf344f41def4', 'research/rectangular-semantic/compatibility-theorem.txt': 'a8129e544a4f662d6172b627905165ca5a0590c2b1e9cad700bcc899fc0eb9ce', 'research/rectangular-semantic/a5-28-27-proof.txt': '622172aaf4e38025c3e3b411d5a71d3b06e3add0294fd3d342d8f54283be7f0c', 'research/translated-partial/complex-certificate.json': '399f102e9bab4d098604971c22d1ec39a787ca39dce84c455791d857e97739f0', 'notes/semantic-bulk-17-note.tex': '652242b05174bb776ffc6165af170df9c8cf220dbd0fc26c24d778f320dbabc8', 'references/rad20/SOURCE.json': '63477ee5103e4c1d0d1665bf2d1cfb91af5bcdef59cac6e46f4d6a1579b8eb2e', 'references/rad20/reports/bulk-resampling-tape-transfer.md': 'cda26d5aca04b9c824eb6c4f50bee564fb7fa908b09a72e76852df5e0b9d2622', 'references/rad20/reports/compact-arbitrary-source-routing.md': '3df36853a181fd5d331811b5c4859a1980116c69f447eb78c40a551ff28cde79', 'references/rad20/reports/downstream-microbox-resampling.md': '9598c236eed7e44ac5eb41cc20f7c23249829e195247d15e2857a34e14222c49', 'references/rad20/reports/downstream-phase-cell-inverse.md': '3cdf492bcb719db4295658604dc202d6a2c5a008b87de43ec54f0107c64db730', 'references/rad20/reports/downstream-semantic-child-guard.md': 'dda9f678ab5afee88b70e405fb70ad47fa2273bd940e9daf603831925d0ef087', 'references/rad20/reports/review-arbitrary-routing.md': 'f18f535a096abae473db71a4ae3f275d0116d7438fb18594d5b160571db670fd', 'references/rad20/reports/review-bulk-resampling.md': '12aefaa9a0eee367fb71e8f910ed5f0094e1203d2caa29836b0c37887c446c29', 'references/rad20/reports/review-phase-cell-inverse.md': '113927dd4fb77a55a457bd5f6da8cbfc7262d0fbc4e9d708b591a1d632e6caf6', 'references/rad20/reports/review-semantic-child-guard.md': '5ded175dbc723df9e45b8a7abc1b729ff77e170d188b0d77102fd8a8f7e0da7e', 'references/rad20/reports/review-balanced-transform.md': '0c3a5b6f17188205d35cd421ef0c35c71f6111698f497e89da3ef7f870fef862', 'references/rad20/reports/downstream-semantic-bulk-assembly.md': 'ccdeaeac7c6a1c08483fea2285a7d089d782f2c18b7be867c3fc9f77457637fd'}
for name,digest in EXPECTED_INPUT_SHA256.items():
 assert hashlib.sha256(source(name).read_bytes()).hexdigest()==digest,name
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

net=json.loads(source('research/rectangular-semantic/certificate.json').read_text())
cc=json.loads(source('research/translated-partial/complex-certificate.json').read_text())
old=net['bit']; cnt=net['counts'];mb,Wb,sb,N=cnt['m'],cnt['W'],cnt['s'],cnt['N']
hist={int(t):int(n) for t,n in cnt['rows'].items()}
# Reconstruct the complete physical histogram from producer records and profiles.
inputs=json.loads(source('research/rectangular-semantic/inputs.json').read_text())
dims=net['dimensions'];assert dims==[28,27,57] and mb==28*27*57
assert N==comb(28,3)*comb(27,3)*comb(57,3)
physical=Counter()
for profile in net['profiles'].values():
 physical[1]+=profile.get('singletons',0)*profile['copies']
 for width in profile['blocks']:physical[width]+=profile['copies']
physical[dims[2]]+=cnt['E'];physical[mb-2*dims[2]]+=cnt['E']
banks=[];loss=0
for axis in dims:
 record=inputs['producers'][str(axis)]['record']
 assert record==net['producer_evidence'][str(axis)]['record']
 v=record['v'];assert v==comb(axis,3)
 assert record['roles']==record['additions']+record['outputs']-record['matches']
 banks.append((N//v)*record['roles']);loss+=(N//v)*record['loss']
 assert sum(r*n for r,n in enumerate(record['histogram']))==axis*record['roles']+2*record['loss']
 physical[1]+=2*N;physical[axis-2]+=2*N
 for rank,multiplicity in enumerate(record['histogram']):
  copies=(N//v)*multiplicity
  if rank==0:continue
  if rank==axis:physical[axis]+=copies
  elif 2*rank>axis:
   physical[1]+=(axis-rank)*copies;physical[2*rank-axis]+=copies
  else:physical[1]+=rank*copies
assert banks==[cnt['B1'],cnt['B2'],cnt['B3']]
assert Wb==2*N+banks[1]+banks[2] and cnt['E']==banks[2]-banks[0]
assert loss==cnt['L'] and sb==Wb*mb-2*N+2*loss
assert dict(physical)==hist
old_mass=sum(t*n for t,n in hist.items()); assert old_mass==sb
baseline_moment,_=moment(hist,mb,Wb,Q(old['saving']),True)
assert baseline_moment==Q(old['moment_upper'])<1
# Exactly2N A5 residuals change their contiguous block partition, not their rank.
hist[1]-=22*(2*N)
hist[22]=hist.get(22,0)+2*N
assert sum(t*n for t,n in hist.items())==sb
assert max(hist)==43038
new_a=Q(12285623,10**12)
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
coeff=wb*hb+wc*hc;degree=96000
assert (hb,hc,wb,wc)==(553,544,44,41)
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
  cutoff_log2_input=cuts,common_cutoff=common,power_checks=checks,negative_controls={**negatives,'old86000stock_fails':86000<coeff*Q(51,25)})

baseline=assembly(Q(old['saving']),Q(1226108866,10**14))
combined=assembly(new_a,Q(1228547206,10**14))
prior=Q(12260937,10**12)
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

result=dict(status='AUTHOR CONDITIONAL PR28 EXTRA22+BALANCED COMPOSITION; INDEPENDENT REVIEW REQUIRED',
 bit=dict(a=new_a,m=mb,W=Wb,s=sb,maxchild=rb,histogram=sorted(hist.items()),moment_upper=bit_moment,strict_gap=1-bit_moment,logarithm_upper=bit_logs,
  modification='2N copies: 29 singleton+25+648 ->7 singleton+25+22+648; actual common-basis pivot lemma supplied separately'),
 complex=dict(a=b,m=mc,W=Wc,s=sc,maxchild=rc,moment_upper=phase_moment,strict_gap=1-phase_moment,logarithm_upper=phase_logs),
 semantic=dict(grouped_scalar_upper=Gates,E=E,literal_charge=literal,strict_gap=E-literal,C0=C0,C1=1),
 physical_histogram_reconstruction=dict(widths=len(physical),banks=banks,loss=loss,producer_records_equal=True),
 product_rows=dict(bit_halving=hb,complex_halving=hc,bit_wire_bits=wb,complex_wire_bits=wc,coefficient=coeff,degree=degree,suffix_slope=4*degree),
 balanced_baseline=baseline,balanced_geometry=combined,PR28_kappa=prior,
 gain_over_PR28=combined['parameters']['kappa']-prior,ratio_over_PR28=combined['parameters']['kappa']/prior,
 named_slot_controls=dict(partitions=partition_count,long_short_shapes=4*partition_count),source_sha256=source_hashes,
 remaining_hypotheses=['Actual same-common-basis width22 pivot lemma and PR28 physical histogram ownership.',
 'Imported finite producer/carrier/dirty-restoration identities, and upstream finite-tape machine theorem.',
 'Pinned RaD semantic/router/balanced/phase-cell/bulk all-size proofs.',
 'BHP threshold; fixed basis/prime/native setup; catalogue domination; strict logarithmic absorption; exact recovery threshold.'])
args.output.write_text(json.dumps(ser(result),sort_keys=True,indent=2)+'\n')
print('PASS: independently rebuilt modified bit/unchanged phase moments;47 strict inequalities for each balanced row; six power-check checkpoints each.')
print('Combined kappa=',combined['parameters']['kappa'],'gap=',float(combined['absorption_gap']),'PR28 improvement=',float(result['gain_over_PR28']))
print('Bit moment gap=',float(1-bit_moment),'phase gap=',float(1-phase_moment),'common log2 input cutoff=',combined['common_cutoff'])
print('Partition/slot fixtures=',partition_count,'/',4*partition_count,'elapsed seconds=',time.monotonic()-started)
