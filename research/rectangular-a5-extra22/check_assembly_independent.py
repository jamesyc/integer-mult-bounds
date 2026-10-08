#!/usr/bin/env python3
"""Independent PR28 rectangular balanced arithmetic review.

No candidate or supplier module is executed or imported. Only Python's standard
library is used. Budget: one process, <60 seconds, <100 MiB. All certifying
numbers are integers/Fractions, including lower moment counter-certificates.
"""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha1, sha256
from math import comb, factorial, prod
from pathlib import Path
import argparse
import json
import resource
import time

resource.setrlimit(resource.RLIMIT_AS, (100*1024*1024, 100*1024*1024))
start = time.monotonic()
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ap = argparse.ArgumentParser()
ap.add_argument('--output', type=Path, default=HERE/'INDEPENDENT_CHECKS.json')
ap.add_argument('--source-root', type=Path, required=True, help='Inherited PR28 repository root for portable mathematical checks.')
ap.add_argument('--assembly-root', type=Path, help='Directory containing the author BALANCED_CHECKS.json and INPUT_MANIFEST.json.')
ap.add_argument('--author-certificate', type=Path, help='Path to the exact frozen author certificate; may be renamed for publication.')
args = ap.parse_args()
source_hashes = {}
ASSEMBLY=args.assembly_root or (ROOT/'semantic_pr28' if (ROOT/'semantic_pr28').is_dir() else HERE)
INPUTROOT=args.source_root or ASSEMBLY/'inputs'
native_names={
 'dimension_attack/pr28/inputs.json':'research/rectangular-semantic/inputs.json',
 'dimension_attack/pr28/certificate.json':'research/rectangular-semantic/certificate.json',
 'pr21/research/translated-partial/complex-certificate.json':'research/translated-partial/complex-certificate.json',
 'pr23/references/rad20/SOURCE.json':'references/rad20/SOURCE.json',
}

def read(rel):
    if rel=='semantic_pr28/BALANCED_CHECKS.json' and args.author_certificate:
        path=args.author_certificate
    elif rel in native_names:
        path=INPUTROOT/native_names[rel]
    elif rel.startswith('semantic_pr28/'):
        path=ASSEMBLY/rel.removeprefix('semantic_pr28/')
    else:
        path=ROOT/rel
    raw = path.read_bytes()
    source_hashes[rel] = sha256(raw).hexdigest()
    return json.loads(raw)

inputs = read('dimension_attack/pr28/inputs.json')
original = read('dimension_attack/pr28/certificate.json')
phase = read('pr21/research/translated-partial/complex-certificate.json')
author = read('semantic_pr28/BALANCED_CHECKS.json')
assert source_hashes['semantic_pr28/BALANCED_CHECKS.json']=='339339b956c6f2932ba8a609ad4cef02fe26731269657379f40ebbb471cf8742'
if (ASSEMBLY/'INPUT_MANIFEST.json').is_file():
    manifest=read('semantic_pr28/INPUT_MANIFEST.json')
else:
    assert args.source_root is not None
    manifest={name:{'sha256':digest} for name,digest in author['source_sha256'].items()}
for native,entry in manifest.items():
    raw=(INPUTROOT/native).read_bytes()
    assert sha256(raw).hexdigest()==entry['sha256']
    if 'bytes' in entry:assert len(raw)==entry['bytes']
    if 'git_blob' in entry:
        assert entry['commit']=='3eafe5a35b572fe38e7d64a55ce5cac1d8838bee'
        assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==entry['git_blob']
    source_hashes['semantic_pr28/inputs/'+native]=entry['sha256']
for name,git_blob in {
    'certificate.json':'a368d91a62fee2b77e93c12b43334adcd671b656',
    'inputs.json':'5872d8319452500d4e81c7ca6b05d820e998e184',
    'compatibility-theorem.txt':'0afc0cd1da3ba4341621bad4897f5c37a6f2fa02',
    'a5-28-27-proof.txt':'ae6f2346f4718ddcad335e5a97c8d733f768d605',
}.items():
    raw=(INPUTROOT/'research/rectangular-semantic'/name).read_bytes()
    assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==git_blob

# Reconstruct the bit histogram from physical stage/local producer profiles,
# rather than trusting the already assembled histogram in either certificate.
dims = (28, 27, 57)
A, Bdim, Kdim = dims
mb = prod(dims)
records = {h: inputs['producers'][str(h)]['record'] for h in dims}
N = prod(records[h]['v'] for h in dims)
banks = {h: N//records[h]['v']*records[h]['roles'] for h in dims}
Wb = 2*N+banks[Bdim]+max(banks[A],banks[Kdim])
loss = sum(N//records[h]['v']*records[h]['loss'] for h in dims)
hist = Counter()
stage_parts = {}

def add(width, copies):
    assert isinstance(width, int) and isinstance(copies, int)
    if width and copies:
        assert 0 < width < mb and copies > 0
        hist[width] += copies

for h in dims:
    record = records[h]
    hh = record['histogram']
    assert N % record['v'] == 0
    assert sum(r*n for r,n in enumerate(hh)) == h*record['roles']+2*h*(h-1)
    for rank, copies in enumerate(hh):
        copies *= N//record['v']
        if rank == h:
            add(h, copies)
        elif 2*rank > h:
            add(1, (h-rank)*copies)
            add(2*rank-h, copies)
        else:
            add(1, rank*copies)
stage_parts['local'] = sorted(hist.items())
for width in (A,Kdim-2*A,A,A,mb-2*(A+Kdim)):
    add(width,banks[A])
for width in (Kdim,mb-2*Kdim):
    add(width,banks[Kdim]-banks[A])
for width in (Bdim,mb-2*Bdim):
    add(width,banks[Bdim])
add(1,2*N*(2*Kdim-1))
for width in (Kdim-2,A*Bdim-2*Kdim+2,mb-2*A*Bdim-2*Kdim+2):
    add(width,2*N)
add(1,2*N*(A+1))
for width in (Bdim-2,A*Bdim-2*(A+Bdim-1)):
    add(width,2*N)
for h in dims:
    add(1,2*N)
    add(h-2,2*N)
assert dict(hist) == {int(k):v for k,v in original['counts']['rows'].items()}
assert (mb,N,Wb,loss) == (43092,280378098000,13904995529880,162580083120)
sb = sum(r*n for r,n in hist.items())
assert sb == original['counts']['s'] == 599193831777559200
assert Wb*mb-sb == 2*N-2*loss > 0
oldhist = dict(hist)
hist[1] -= 44*N
hist[22] += 2*N
assert all(n>0 and 0<t<mb for t,n in hist.items())
assert sum(r*n for r,n in hist.items()) == sb
assert sorted(hist.items()) == [tuple(x) for x in author['bit']['histogram']]
assert max(hist) == 43038 and len(hist) == 49

mc,Wc,sc = phase['m'],phase['W'],phase['s']
phist = {int(k):v for k,v in phase['child_counts'].items()}
assert (mc,Wc,sc,max(phist)) == (21952,2085111546336,45772350635112192,21924)
assert sum(r*n for r,n in phist.items()) == sc
assert all(n>0 and 0<r<mc for r,n in phist.items())
assert Wc*mc-sc == phase['D'] == 18030055680
assert all(F(r*n,Wc*mc)==F(phase['rank_mass_weights'][str(r)]) for r,n in phist.items())

def ceil(x):
    assert isinstance(x,F)
    return -(-x.numerator//x.denominator)

def log_interval(ratio):
    assert isinstance(ratio,F) and ratio>1
    exponent=0
    while ratio>2:
        ratio/=2
        exponent+=1
    def atanh(x):
        z=(x-1)/(x+1)
        lower=2*sum((z**(2*j+1)/(2*j+1) for j in range(40)),F(0))
        upper=lower+2*z**81/(81*(1-z*z))
        return lower,upper
    lo,hi=atanh(ratio)
    l2,h2=atanh(F(2))
    lo+=exponent*l2
    hi+=exponent*h2
    scale=10**18
    lo*=scale
    hi*=scale
    return F(lo.numerator//lo.denominator,scale),F(ceil(hi),scale)

def moments(m,W,counts,saving):
    lower,upper=F(0),F(0)
    logs={}
    for r,n in sorted(counts.items()):
        logs[r]=lo,hi=log_interval(F(m,r))
        u,v=saving*lo,saving*hi
        assert 0<u<=v<1
        el=sum((u**j/factorial(j) for j in range(7)),F(0))
        eu=sum((v**j/factorial(j) for j in range(7)),F(0))+v**7/(factorial(7)*(1-v/8))
        lower+=F(r*n,m*W)*el
        upper+=F(r*n,m*W)*eu
    return lower,upper,logs

a,b = F(12285623,10**12),F(9,500000)
baseline_a=F(12261239,10**12)
_,baseline_upper,baseline_logs=moments(mb,Wb,oldhist,baseline_a)
assert baseline_upper<1
bit_lower,bit_upper,bit_logs=moments(mb,Wb,hist,a)
phase_lower,phase_upper,phase_logs=moments(mc,Wc,phist,b)
next_lower,_,_=moments(mb,Wb,hist,a+F(1,10**12))
old_lower,_,_=moments(mb,Wb,oldhist,a)
assert bit_upper<1 and phase_upper<1
assert next_lower>1 and old_lower>1
# Independently verify every saved logarithm upper endpoint and reconstruct
# the exact author's enclosure without executing the author implementation.
saved_moments={}
for name,m,W,counts,saving,logs in [('bit',mb,Wb,hist,a,bit_logs),('complex',mc,Wc,phist,b,phase_logs)]:
    total=F(0)
    for r,n in counts.items():
        ell=F(author[name]['logarithm_upper'][str(r)])
        assert ell>=logs[r][1]
        u=saving*ell
        assert 0<u<1
        bound=1+u+u*u/(2*(1-u/3)) if name=='bit' else 1/(1-u)
        total+=F(r*n,m*W)*bound
    assert total==F(author[name]['moment_upper'])<1
    assert 1-total==F(author[name]['strict_gap'])
    saved_moments[name]=total
baseline_saved=F(0)
for width,copies in oldhist.items():
    u=baseline_a*F(author['bit']['logarithm_upper'][str(width)])
    assert baseline_logs[width][1]<=F(author['bit']['logarithm_upper'][str(width)])
    baseline_saved+=F(width*copies,mb*Wb)*(1+u+u*u/(2*(1-u/3)))
assert baseline_saved==F(original['bit']['moment_upper'])<1

gate_bound=3*comb(28,3)**2*(4*64298+4*comb(28,3)+4)
E=64*(Wc+mc+1)**3
literal=2*gate_bound*Wc**2+8*sc+4*Wc+4+32*mc
S=sc+E
C0=32*mc*S*S
assert E>literal and 2*S*(mc-max(phist))>=sc+E and C0>2*S+18
for cutoff in (mc,mc**2,10**9):
    for e0 in (mc-1,mc,mc+1,10*mc+1,mc**3,10**12):
        e=e0
        value=0
        while e>=max(mc,cutoff):
            f=e//mc
            value+=sc*f+E
            e=max(phist)*f
        assert value+8*e<=2*S*e0

def halving(m,r):
    power=1
    while m**power<=2*r**power:
        power+=1
    assert m**(power-1)<=2*r**(power-1)
    return power

hb,hc=halving(mb,max(hist)),halving(mc,max(phist))
wb,wc=Wb.bit_length(),Wc.bit_length()
assert (hb,hc,wb,wc)==(553,544,44,41)
coefficient=hb*wb+hc*wc
degree=96000
assert coefficient==46636 and F(degree)-F(51,25)*coefficient==F(21564,25)>0
assert max(Wb,Wc)<Wb*Wc
assert F(86000)-F(51,25)*coefficient<0

h,beta=F(1,10**12),F(1,4)
q=a*(1-2*h)
c=q+h/4
epsilon=(1-h)/(1+q)
gain=epsilon*q
r=(gain+1-epsilon)/2
delta=h/8
tau,sigma=1-a,1-b
lp=1-q
lam=(tau+lp)/2
internal=tau+(1-beta)*max(sigma-tau,F(0))
leaf=sigma+beta*(1-sigma)
kappa=F(1228547206,10**14)
slacks={
 'bit_positive':a,'phase_above_bit':b-a,'phase_below_1_32':F(1,32)-b,
 'beta_positive':beta,'beta_below_one':1-beta,'phase_leaf_headroom':(1-beta)*b-a,
 'q_positive':q,'q_below_internal_saving':1-internal-q,'q_below_leaf_saving':1-leaf-q,
 'c_positive':c,'c_below_one':1-c,'c_above_q':c-q,
 'lambda_above_tau':lam-tau,'lambda_above_sigma':lam-sigma,'lambda_above_internal':lam-internal,
 'lambda_prime_above_lambda':lp-lam,'lambda_prime_below_one':1-lp,
 'compact_leaf':lp-leaf,'compact_reservations':lp-(1-c),
 'epsilon_positive':epsilon,'epsilon_below_one':1-epsilon,'semantic_guard':1-epsilon,
 'K_geometry':1-epsilon*(1+c),'K_superlog':epsilon*c,'record_suffix':1-epsilon,
 'gaussian_local':1-epsilon-delta,'gaussian_boundary':r-delta,'gamma':1-epsilon-r,
 'phase_cell':epsilon-(1-r)/2,'prime_packing':1-epsilon,'alpha_positive':r,
 'alpha_below_one':1-r,'alpha_below_quarter':F(1,4)-r,'delta_positive':delta,
 'delta_below_eighth':F(1,8)-delta,'short_record_fallback':epsilon-a,
 'small_field':1-epsilon-gain,'artificial_boundary':8-epsilon+r-delta-gain,
 'source_halo':8-epsilon-3,'target_halo':8-epsilon-3,'halo_vs_Jw':3-2-(1-r)/2,
 'literal_guard':F(E-literal),'product_stock':F(degree)-F(coefficient*51,25),
}
margins=[1-epsilon,a,gain,a,min(1-epsilon-delta,r-delta),1-epsilon-delta,epsilon]
slacks.update({'saving_'+str(i):margin-kappa for i,margin in enumerate(margins,1)})
assert all(isinstance(v,F) and v>0 for v in slacks.values())
assert min(margins)==gain and 1-epsilon-gain==h and 1-epsilon-r==h/2
assert 1-epsilon*(1+c)==h-epsilon*h/4
assert 1-epsilon*(1+c)<kappa
assert 1-epsilon*F(19991,10000)<0
assert a*(1-epsilon)<kappa
assert a<F(1,65536)
assert kappa>F(12260937,10**12)
assert gain==F(author['balanced_geometry']['minimum'])
assert gain-kappa==F(author['balanced_geometry']['absorption_gap'])
assert len(author['balanced_geometry']['slacks'])==47
assert all(F(x)>0 for x in author['balanced_geometry']['slacks'].values())
slack_name_map={
 'a_positive':'bit_positive','b_above_a':'phase_above_bit','b_small':'phase_below_1_32',
 'beta_positive':'beta_positive','beta_small':'beta_below_one',
 'phase_leaf_above_bit':'phase_leaf_headroom','q_positive':'q_positive',
 'q_below_internal':'q_below_internal_saving','q_below_leaf':'q_below_leaf_saving',
 'c_positive':'c_positive','c_small':'c_below_one','c_above_q':'c_above_q',
 'lambda_above_tau':'lambda_above_tau','lambda_above_sigma':'lambda_above_sigma',
 'lambda_above_internal':'lambda_above_internal',
 'lambda_prime_above_lambda':'lambda_prime_above_lambda',
 'lambda_prime_below_one':'lambda_prime_below_one','compact_leaf':'compact_leaf',
 'compact_reservations':'compact_reservations','epsilon_positive':'epsilon_positive',
 'epsilon_below_one':'epsilon_below_one','semantic_guard':'semantic_guard',
 'K_geometry':'K_geometry','K_dominates_log':'K_superlog','record_suffix':'record_suffix',
 'gaussian_local':'gaussian_local','gaussian_boundary':'gaussian_boundary','gamma':'gamma',
 'phase_cell':'phase_cell','prime_packing':'prime_packing','alpha_positive':'alpha_positive',
 'alpha_below_one':'alpha_below_one','alpha_below_quarter':'alpha_below_quarter',
 'delta_positive':'delta_positive','delta_small':'delta_below_eighth',
 'short_record_fallback':'short_record_fallback','small_field_exposure':'small_field',
 'artificial_boundary':'artificial_boundary','literal_scalar_guard':'literal_guard',
 'row_stock_degree':'product_stock',
}
slack_name_map.update({f'margin_{i}_above_kappa':f'saving_{i}' for i in range(1,8)})
assert set(slack_name_map)==set(author['balanced_geometry']['slacks'])
assert all(slacks[ours]==F(author['balanced_geometry']['slacks'][theirs]) for theirs,ours in slack_name_map.items())

# Verify the independent conclusion that balanced layout improves the
# unchanged PR28 histogram. This uses the same accepted inequalities but
# freshly derived parameters; the optional new geometry is unnecessary.
def baseline_assembly():
    aa=baseline_a
    qq=aa*(1-2*h)
    cc=qq+h/4
    ee=(1-h)/(1+qq)
    gg=ee*qq
    rr=(gg+1-ee)/2
    llp=1-qq
    ll=(1-aa+llp)/2
    kk=F(1226108866,10**14)
    mm=[1-ee,aa,gg,aa,min(1-ee-delta,rr-delta),1-ee-delta,ee]
    checks=[aa,b-aa,F(1,32)-b,beta,1-beta,(1-beta)*b-aa,
        qq,aa-qq,1-leaf-qq,cc,1-cc,cc-qq,ll-(1-aa),ll-sigma,
        llp-ll,1-llp,llp-leaf,llp-(1-cc),ee,1-ee,
        1-ee*(1+cc),ee*cc,1-ee-delta,rr-delta,1-ee-rr,
        ee-(1-rr)/2,rr,1-rr,F(1,4)-rr,delta,F(1,8)-delta,
        ee-aa,1-ee-gg,8-ee+rr-delta-gg,8-ee-3,3-2-(1-rr)/2,
        F(degree)-F(coefficient*51,25),F(E-literal)]+[x-kk for x in mm]
    assert all(isinstance(x,F) and x>0 for x in checks)
    assert min(mm)==gg and 1-ee-gg==h and 1-ee-rr==h/2
    assert 1-ee*(1+cc)<kk and 1-ee*F(19991,10000)<0
    assert aa*(1-ee)<kk and aa<F(1,65536)
    assert kk>F(12260937,10**12) and kappa>kk
    saved=author['balanced_baseline']
    parameters=dict(a=aa,b=b,h=h,beta=beta,q=qq,c=cc,epsilon=ee,
        lambda_=ll,lambda_prime=llp,r=rr,delta=delta,kappa=kk)
    assert parameters=={key:F(value) for key,value in saved['parameters'].items()}
    assert mm==[F(x) for x in saved['margins']]
    assert gg==F(saved['minimum']) and gg-kk==F(saved['absorption_gap'])
    # Explicit numeric cutoffs apply to this row as well.
    threshold=14000000000000
    aa_k,cc_k,bb_k,ss_k=(ceil(1/x) for x in (rr,ee*cc,1-ee,ee*beta))
    assert threshold*(1-ee-rr)>=7
    assert threshold*(1-ee)>=(2*C0).bit_length()
    assert threshold*(ee-(1-rr)/2)>=9
    assert threshold*(1-ee*(1+cc))>=3
    assert threshold>=max(2*aa_k,2*cc_k,2*bb_k,2*ss_k,25)
    for shift in range(6):
        length=threshold*2**shift
        for denominator,rhs in [(aa_k,8*length+64),(cc_k,32*length+192),
                (bb_k,16*length+56),(bb_k,4*degree*(length+8)),(ss_k,4*max(mb,mc))]:
            assert length//denominator>=rhs.bit_length()
    return {'parameters':parameters,'margins':mm,'minimum':gg,'kappa':kk,
        'absorption_gap':gg-kk,'strict_checks':len(checks),'bit_upper_gap':1-baseline_upper}

baseline_check=baseline_assembly()

# Uniform all-size conclusion: for each positive rational theta, choose
# k=ceil(1/theta). Since 2^(L/k)/(A*L+B) is increasing once L>=2k,
# verified inequalities then persist. Integer exponents are only sufficient
# witnesses; floor fluctuations need not be falsely called monotonic.
L=14000000000000
ka,km,kb,ks=(ceil(1/x) for x in (r,epsilon*c,1-epsilon,epsilon*beta))
assert L*(1-epsilon-r)>=7 and L*(1-epsilon)>=(2*C0).bit_length()
assert L*(epsilon-(1-r)/2)>=9 and L*(1-epsilon*(1+c))>=3
assert L>=max(2*ka,2*km,2*kb,2*ks,25)
powers=[]
for j in range(6):
    x=L*2**j
    tests={'alpha':(x//ka,8*x+64),'compact':(x//km,32*x+192),
           'period':(x//kb,16*x+56),'rows':(x//kb,4*degree*(x+8)),
           'leaf':(x//ks,4*max(mb,mc))}
    assert all(exponent>=rhs.bit_length() for exponent,rhs in tests.values())
    powers.append({'log2_input':x,'tests':{name:{'exponent':p,'rhs':v,'rhs_bits':v.bit_length()} for name,(p,v) in tests.items()}})

# Independent positional bijections over all small long/short shapes, using
# destination keys instead of the author's assembled-list construction.
layout_cases=0
for n in range(1,65):
    for K in range(1,n+1):
        qgroups=n//K
        width,extra=divmod(n,qgroups)
        widths=[width+(j<extra) for j in range(qgroups)]
        assert sum(widths)==n and all(K<=w<2*K for w in widths)
        level_group={}
        end=n
        for group,w in enumerate(widths):
            for level in range(end-w,end):level_group[level]=group
            end-=w
        for axis_count in (1,2,3):
            for flags in range(2**axis_count):
                original_slots=[(axis,level) for axis in range(axis_count) for level in range(n+(flags>>axis&1)-1,-1,-1)]
                def key(slot):
                    axis,level=slot
                    return (-1,axis,0) if level==n else (level_group[level],axis,-level)
                balanced=sorted(original_slots,key=key)
                inverse={slot:position for position,slot in enumerate(balanced)}
                assert len(inverse)==len(original_slots)
                assert [balanced[inverse[slot]] for slot in original_slots]==original_slots
                for axis in range(axis_count):
                    assert [level for i,level in balanced if i==axis]==list(range(n+(flags>>axis&1)-1,-1,-1))
                layout_cases+=1

rad=read('pr23/references/rad20/SOURCE.json')
assert rad['commit']=='45d9b60355872041f9275f77c057514def0d45bc'
for rel,digest in author['source_sha256'].items():
    if rel.startswith('references/rad20/reports/'):
        local=INPUTROOT/rel
        assert sha256(local.read_bytes()).hexdigest()==digest==rad['source_sha256'][rel.removeprefix('references/rad20/')]

def serial(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):serial(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [serial(v) for v in value]
    return value

result={
 'status':'PASS conditional arithmetic and generic interface transfer; width-22 geometry is a separately accepted prerequisite',
 'portable_scope':'Native pinned inputs and exact mathematical calculations; public source hashes record the documentary adaptation.',
 'source_sha256':source_hashes,'reviewer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'bit':{'m':mb,'W':Wb,'N':N,'rank_mass':sb,'histogram':sorted(hist.items()),'log_intervals':bit_logs,
        'saving':a,'upper_gap':1-bit_upper,'saved_upper_gap':1-saved_moments['bit'],
        'next_grid_true_excess_lower':next_lower-1,'unregrouped_true_excess_lower':old_lower-1},
 'complex':{'m':mc,'W':Wc,'rank_mass':sc,'log_intervals':phase_logs,'upper_gap':1-phase_upper,'saved_upper_gap':1-saved_moments['complex']},
 'semantic':{'grouped_gates':gate_bound,'E':E,'literal':literal,'C0':C0},
 'stock':{'bit_depth':hb,'complex_depth':hc,'coefficient':coefficient,'degree':degree},
 'parameters':{'a':a,'b':b,'h':h,'beta':beta,'q':q,'c':c,'epsilon':epsilon,'r':r,'delta':delta,'lambda':lam,'lambda_prime':lp},
 'slacks':slacks,'margins':margins,'minimum':gain,'kappa':kappa,'absorption_gap':gain-kappa,
 'improvement_over_PR28':kappa-F(12260937,10**12),
 'unchanged_PR28_balanced':baseline_check,
 'negative_controls':['original-prefix charge','old nonlinear guard','separate exposure','2^-16 ceiling','old 86000 stock','next bit grid actual moment','old histogram at new saving'],
 'cutoff_log2_input':L,'power_checks':powers,'named_slot_shapes':layout_cases,
 'elapsed_seconds':time.monotonic()-start,
 'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
}
args.output.write_text(json.dumps(serial(result),indent=2,sort_keys=True)+'\n')
print('PASS:',len(slacks),'strict Fraction slacks;',layout_cases,'layout cases; kappa',kappa)
print('Exact gain minus kappa:',gain-kappa)
print('All proof certifications used integers/Fractions; elapsed seconds is timing metadata only.')
