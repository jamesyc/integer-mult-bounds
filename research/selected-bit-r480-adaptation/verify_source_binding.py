#!/usr/bin/env python3
"""Bounded read-only raw/Lean projection comparison. No supplier or Lean execution."""
from pathlib import Path
import ast,datetime,gzip,hashlib,io,json,re,resource,subprocess,time
resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(20,20));t=time.monotonic()
G=Path('/workspace/shared/integer-mult-git/worktrees/signed');D=Path(__file__).parent;REF='7dfa22b109996e48db68daac3706e7a49a43002b';H=lambda b:hashlib.sha256(b).hexdigest()
def show(p,limit=1024**2):
 sz=int(subprocess.check_output(['git','cat-file','-s',REF+':'+p],cwd=G));assert sz<=limit
 b=subprocess.check_output(['git','show',REF+':'+p],cwd=G);assert len(b)==sz;return b

def pairs(xs):
 d={}
 for k,v in xs:assert k not in d;d[k]=v
 return d

def strict(b):return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def decode(b):
 assert len(b)<=65536
 with gzip.GzipFile(fileobj=io.BytesIO(b))as f:r=f.read(300001)
 assert len(r)<=300000;return r,strict(r)
rel='research/e8-r480-dead-totals/data/bitE8mut-r480.json.gz';compressed=show(rel,65536);assert H(compressed)=='92e399e9a486b55229b5624632ac54f800dd9e022f2aee97f1e5f264bbc0ef5c';raw,new=decode(compressed)
assert H(raw)=='8639e22008c24a5690dd250eba702fe5fca85ddd036dcbec20baba77b7e213ba'
manifest=strict(show('research/e8-r480-dead-totals/MANIFEST.json'));assert manifest['files']['data/bitE8mut-r480.json.gz']==H(compressed)
oldcompressed=(G/'research/e8-bit-carrier-skeleton/data/bit/bitE8mut-r489.json.gz').read_bytes();assert H(oldcompressed)=='835eb96e147740fc7454f8cfb3dbd34ae89524b1dbd89a61e9288eae8ab6a5b9';oldraw,old=decode(oldcompressed)
assert set(old)==set(new)=={'format','h','v','R','lines','frames','A','B','C','D','start','final','ret','scatter','form','coords'}
boundary=(G/'research/selected-bit-carrier-preparation/SelectedBitCarrierBoundaryData.lean').read_text();phase=(G/'research/selected-bit-carrier-successor/SelectedBitCarrierPhaseBData.lean').read_text();candidate=(D/'SelectedR480Boundary.lean').read_text()
def literal(s,name):
 rhs=re.search(r'^def '+name+r'\s*:[^\n]*? := (.*)$',s,re.M).group(1)
 tree=ast.parse(rhs,mode='eval');assert all(isinstance(n,(ast.Expression,ast.List,ast.Tuple,ast.Constant,ast.Load,ast.UnaryOp,ast.USub)) for n in ast.walk(tree))
 return ast.literal_eval(tree)
projected={k:literal(boundary,k) for k in ['h','v','format','form','lines','frames']}
projected.update(R=literal(candidate,'R'),ret=literal(candidate,'ret'),start=literal(boundary,'start')[:720],final=literal(boundary,'final')[:720],B=[list(g[:2])+[g[2]] for g in literal(phase,'phaseB')],scatter=literal(phase,'scatter'))
for k,v in projected.items():assert v==new[k],k
for k in ['h','v','format','form','lines','frames','B','scatter']:assert old[k]==new[k]
assert new['start']==old['start'][:720] and new['final']==old['final'][:720]
assert new['ret']==[701,682,693,700,661,695,717,675,706]
assert new['h']==8 and new['v']==120 and new['R']==480 and len(new['frames'])==672
assert len(new['start'])==len(new['final'])==720 and all(0<=f<672 for f in new['start']+new['final'])
assert new['start'][120:]==[0]*600 and new['final'][:120]==[1]*120 and new['final'][240:]==[1]*480
assert all(new['frames'][new['start'][r]]==[r] for r in range(120))
assert len(new['B'])==240 and sum(len(g[2])for g in new['B'])==600
assert all(type(f)is int and 0<=f<672 and type(d)is int and 120<=d<240 and all(type(r)is int and 0<=r<720 and not 120<=r<240 for r in ss)for f,d,ss in new['B'])
assert len(new['scatter'])==120 and sum(map(len,new['scatter']))==568
assert all(len(set(row))==len(row) and all(type(k)is int and 0<=k<9 for k in row)for row in new['scatter'])
assert len(set(new['ret']))==9 and all(240<=r<720 for r in new['ret'])
windows=[(r,[120+j for j,row in enumerate(new['scatter'])if k in row]) for k,r in enumerate(new['ret'])]
assert [len(ds)for r,ds in windows]==[120]+[56]*8
sources=[]
for p in sorted(D.glob('*.lean')):
 s=p.read_text();sources.append(dict(path=str(p),sha256=H(p.read_bytes()),bytes=p.stat().st_size,imports=re.findall(r'^import (\S+)',s,re.M),public_probes=re.findall(r'^#print axioms (\S+)',s,re.M)))
trans=json.loads((D/'SOURCE_TRANSFORM.json').read_text())
for r in trans['files']:
 oldbytes=Path(r['preimage']).read_bytes();assert H(oldbytes)==r['preimage_sha256'];s=oldbytes.decode()
 for x in r['ordered_replacements']:assert s.count(x['old'])==x['occurrences'];s=s.replace(x['old'],x['new'])
 assert s.encode()==Path(r['candidate']).read_bytes() and H(s.encode())==r['candidate_sha256']
paths=[rel,'research/e8-r480-dead-totals/MANIFEST.json','research/e8-r480-dead-totals/code/adapt.py','research/e8-bit-carrier-skeleton/code/bit/export_records.py','certificates/selected-result.json','research/community-family533-audit/pr535-ASSEMBLY.json']
pins=[]
for p in paths:
 b=show(p);pins.append(dict(path=p,sha256=H(b),bytes=len(b),git_blob=subprocess.check_output(['git','rev-parse',REF+':'+p],cwd=G,text=True).strip()))
print(json.dumps(dict(status='PASS_BOUNDED_RAW_LITERAL_AND_PARAMETER_BINDING_NO_COMPILER',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),observed_snapshot=REF,source_bindings=pins,decoded=dict(sha256=H(raw),bytes=len(raw)),projected_fields=list(projected),sources=sources,shape=dict(v=120,R=480,registers=720,extended_registers=721,temp=720,frames=672,B_gates=240,B_operands=600,scatter_rows=120,scatter_indices=568,ret=new['ret'],retained_major_add_counts=[len(ds)for _,ds in windows],COPY=9,ADD=568,ERASE=9),proof_transport='Fresh Fin720/Fin721 instances; no equality with old Fin729/Fin730 typed proofs. Exact raw aliases only.',exclusions=['A/C/D semantics','physical frame realization and copy space','full selected multiplier theorem','restoration of arbitrary incoming temporary'],resources=dict(elapsed_seconds=time.monotonic()-t,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,CPU_seconds=20,AS_bytes=256*1024**2,decoded_cap=300000),upstream_code_executed=False,compiler_executed=False),indent=2))
