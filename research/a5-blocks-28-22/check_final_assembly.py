#!/usr/bin/env python3
"""Independent final assembly check. Executes no supplier or author code.
Standard-library only; expected <2 s/<64 MiB, outer run cap 60 s.
Native PR27 reproduction: --source-root REPOSITORY --output review.json
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from math import comb
import argparse,json,time

ap=argparse.ArgumentParser()
ap.add_argument('--source-root',type=Path)
ap.add_argument('--output',type=Path,default=Path(__file__).with_name('FINAL_ASSEMBLY_CHECKS.json'))
args=ap.parse_args()
start=time.monotonic()
base=Path(__file__).resolve().parent.parent
if args.source_root:
    bitpath=args.source_root/'certificates/endpoint-gauge-network.json'
    phasepath=args.source_root/'research/translated-partial/complex-certificate.json'
else:
    bitpath=base/'pr24/certificates/endpoint-gauge-network.json'
    phasepath=base/'pr21/research/translated-partial/complex-certificate.json'
bit=json.loads(bitpath.read_text())['bit']
phase=json.loads(phasepath.read_text())
bc=bit['counts'];mb,Wb,N=bc['m'],bc['W'],bc['N']
mc,Wc,s=phase['m'],phase['W'],phase['s']
hist=dict(bit['child_width_multiplicities'])
hist[1]-=100*N
for width in (28,22):hist[width]=hist.get(width,0)+2*N
assert sum(t*n for t,n in hist.items())==bc['total_rank']
phist={int(t):n for t,n in phase['child_counts'].items()}
assert sum(t*n for t,n in phist.items())==s
assert all(n>0 and 0<t<mb for t,n in hist.items())
assert all(n>0 and 0<t<mc for t,n in phist.items())
a,b=F(2405333,200000000000),F(9,500000)

def up_log(x):
    k=0
    while x>2:x/=2;k+=1
    def series(y):
        z=(y-1)/(y+1)
        return 2*sum((z**(2*j+1)/(2*j+1) for j in range(32)),F(0))+2*z**65/(65*(1-z*z))
    y=(series(x)+k*series(F(2)))*10**15
    return F(-(-y.numerator//y.denominator),10**15)
def moment(m,W,counts,saving):
    total=F(0)
    for t,n in counts.items():
        u=saving*up_log(F(m,t))
        assert 0<u<3
        total+=F(n*t,W*m)*(1+u+u*u/(2*(1-u/3)))
    assert total<1
    return total
bm,cm=moment(mb,Wb,hist,a),moment(mc,Wc,phist,b)

Gscalar=3*comb(28,3)**2*(4*64298+4*comb(28,3)+4)
E=64*(Wc+mc+1)**3
charge=2*Gscalar*Wc**2+8*s+4*Wc+4+32*mc
B=s+E;C0=32*mc*B**2
assert E>charge and 2*B*(mc-max(phist))>=s+E and C0>2*B+18
def depth(m,r):
    j=1
    while m**j<=2*r**j:j+=1
    assert m**(j-1)<=2*r**(j-1)
    return j
db,dc=depth(mb,max(hist)),depth(mc,max(phist))
wb,wc=Wb.bit_length(),Wc.bit_length()
assert (db,dc,wb,wc)==(444,544,44,41)
coeff=db*wb+dc*wc
assert coeff==41840 and F(51,25)*coeff<86000

h,beta=F(1,10**12),F(1,4)
q=a*(1-2*h);c=q+h/4;eps=(1-h)/(1+q)
gain=eps*q;r=(gain+1-eps)/2;delta=h/8
tau,sigma=1-a,1-b;lp=1-q;lam=(tau+lp)/2
leaf=sigma+beta*(1-sigma);kappa=F(1202652036,10**14)
constraints={
 'a':a,'complex_above_bit':b-a,'complex_small':F(1,32)-b,
 'beta':beta,'one_minus_beta':1-beta,'phase_leaf_headroom':(1-beta)*b-a,
 'q':q,'internal_headroom':a-q,'leaf_headroom':1-leaf-q,
 'c':c,'c_below_one':1-c,'reserve_headroom':c-q,
 'lambda_tau':lam-tau,'lambda_sigma':lam-sigma,'lambda_order':lp-lam,
 'lambda_prime_below_one':1-lp,'compact_leaf':lp-leaf,'compact_reserve':lp-(1-c),
 'epsilon':eps,'linear_guard':1-eps,'K_geometry':1-eps*(1+c),'K_log':eps*c,
 'record_suffix':1-eps,'phase_local':1-eps-delta,'phase_boundary':r-delta,
 'gamma':1-eps-r,'cell_vs_band':eps-(1-r)/2,'prime':1-eps,
 'alpha':r,'alpha_below_one':1-r,'alpha_below_quarter':F(1,4)-r,
 'delta':delta,'delta_below_eighth':F(1,8)-delta,'short_records':eps-a,
 'small_field':1-eps-gain,'artificial_boundary':8-eps+r-delta-gain,
 'source_halo':8-eps-3,'target_halo':8-eps-3,'halo_vs_Jw':3-2-(1-r)/2,
 'stock_gap':86000-F(51,25)*coeff,'scalar_charge_gap':E-charge,
}
margins=[1-eps,a,gain,a,min(1-eps-delta,r-delta),1-eps-delta,eps]
for j,value in enumerate(margins,1):constraints['saving_'+str(j)]=value-kappa
assert all(v>0 for v in constraints.values())
assert min(margins)==gain and 1-eps-gain==h and 1-eps-r==h/2
assert 1-eps*(1+c)==h-eps*h/4
assert 1-eps*(1+c)<kappa
assert 1-eps*F(19991,10000)<0
assert a*(1-eps)<kappa and F(1,65536)>a
assert gain-kappa==F(3676762446146321311,3561296391257122421462500000000000)
assert kappa-F(119720853,10**13)==F(5443506,10**14)

def ceil(x):return -(-x.numerator//x.denominator)
L=14000000000000
ka,km,kb,ks=ceil(1/r),ceil(1/(eps*c)),ceil(1/(1-eps)),ceil(1/(eps*beta))
assert L*(1-eps-r)>=7
assert L*(1-eps)>=(2*C0).bit_length()
assert L*(eps-(1-r)/2)>=9
assert L*(1-eps*(1+c))>=3
assert L>=max(2*ka,2*km,2*kb,25)
powers=[]
for j in range(6):
    t=L*2**j
    tests={'alpha':(t//ka,8*t+64),'compact':(t//km,32*t+192),
           'period':(t//kb,16*t+56),'rows':(t//kb,344000*(t+8)),
           'leaf':(t//ks,4*max(mb,mc))}
    assert all(power>=rhs.bit_length() for power,rhs in tests.values())
    powers.append({'log2_input':t,'tests':{name:{'power':v[0],'rhs':v[1],'rhs_bits':v[1].bit_length()} for name,v in tests.items()}})

def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x
out={'status':'PASS: conditional A5-regrouped balanced assembly; geometry theorem is a separate prerequisite',
 'source_sha256':{str(bitpath):sha256(bitpath.read_bytes()).hexdigest(),str(phasepath):sha256(phasepath.read_bytes()).hexdigest()},
 'reviewer_source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'moments':{'bit_upper':bm,'complex_upper':cm},
 'scalar':{'G':Gscalar,'E':E,'C0':C0,'charge':charge},
 'stock':{'bit_depth':db,'complex_depth':dc,'bit_bits':wb,'complex_bits':wc,'coefficient':coeff,'degree':86000},
 'parameters':{'a':a,'b':b,'h':h,'beta':beta,'q':q,'c':c,'epsilon':eps,'r':r,'delta':delta,'lambda':lam,'lambda_prime':lp},
 'kappa':kappa,'minimum':gain,'gap':gain-kappa,'constraints':constraints,'power_checks':powers,
 'negative_controls':['original_prefix','old_nonlinear_guard','separate_exposure','unattainable_2_minus16'],
 'elapsed_seconds':time.monotonic()-start}
args.output.write_text(json.dumps(serial(out),indent=2,sort_keys=True)+'\n')
print('PASS',len(constraints),'strict constraints;',len(powers),'cutoff checkpoints; kappa',float(kappa),'gap',float(gain-kappa))
