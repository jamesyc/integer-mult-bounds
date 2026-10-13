#!/usr/bin/env python3
"""Strict bounded current799 gauge44 source projection. No upstream code imports or supplier evaluation."""
from pathlib import Path
import collections, datetime, gzip, hashlib, io, json, re, resource, time
START=time.monotonic()
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
HERE=Path(__file__).resolve().parent
LOCAL=Path('/workspace/scratch/c569c316cd54/recovery_20261011/new_main_f567884_artifacts/extracted/native/local')
MAX=16*1024**2
sha=lambda b:hashlib.sha256(b).hexdigest()
def json_raw(raw):
 if len(raw)>MAX:raise ValueError('JSON exceeds16MiB')
 def pairs(xs):
  out={}
  for k,v in xs:
   if k in out:raise ValueError('duplicate key')
   out[k]=v
  return out
 def invalid(_):raise ValueError('nonfinite')
 return json.loads(raw.decode('utf8'),object_pairs_hook=pairs,parse_constant=invalid)
def integer(x,lo=None,hi=None):
 if type(x) is not int or (lo is not None and x<lo) or (hi is not None and x>=hi):raise ValueError('integer/range')
 return x
def arr(x,n=None):
 if type(x) is not list or (n is not None and len(x)!=n):raise ValueError('array/arity')
 return x
def frame(x):return integer(x,0,1005)
def reg(x):
 arr(x,2)
 if x[0]=='L':return integer(x[1],0,728)
 if x[0]=='C':return 728+integer(x[1],0,8)
 raise ValueError('register kind')
def coeff(n,d):
 integer(n);integer(d)
 if d==0:raise ValueError('zero denominator')
 return [n,d]
def decode_row(i,row,keymap):
 arr(row)
 if not row:raise ValueError('empty event')
 if row[0]=='climb':
  arr(row,6)
  if row[1]!='A':raise ValueError('wrong phase')
  r=integer(row[2],0,728);a,b,k=row[3:]
  frame(a);frame(b);integer(k,1,10)
  if (a,b) not in keymap:raise ValueError('missing directed child')
  ordinal,rank=keymap[a,b]
  if rank!=k:raise ValueError('directed rank mismatch')
  return {'sourceIndex':i,'event':['relabel',r,a,b],'scalarFrame':None,'childRef':[ordinal,k]}
 if row[0]!='scalar':raise ValueError('not a selected scalar/climb row')
 arr(row,3);e=arr(row[1]);f=frame(row[2])
 if not e:raise ValueError('empty scalar')
 if e[0]=='add':arr(e,5);event=['add',reg(e[1]),reg(e[2]),coeff(e[3],e[4])]
 elif e[0]=='scale':arr(e,4);event=['scale',reg(e[1]),coeff(e[2],e[3])]
 else:raise ValueError('unsupported slice scalar')
 return {'sourceIndex':i,'event':event,'scalarFrame':f,'childRef':None}
def lean_row(row):
 e=row['event'];tag=e[0]
 if tag=='relabel':event='.relabel '+' '.join(map(str,e[1:]))
 else:event='.'+tag+' '+' '.join(map(str,e[1:-1]))+f' (({e[-1][0]}), ({e[-1][1]}))'
 f='none' if row['scalarFrame'] is None else 'some '+str(row['scalarFrame'])
 ref='none' if row['childRef'] is None else 'some ('+', '.join(map(str,row['childRef']))+')'
 return f'  ⟨{row["sourceIndex"]}, {event}, {f}, {ref}⟩'
def emit_array(name,ty,values):return f'def {name} : Array {ty} := #[\n  '+',\n  '.join(values)+'\n]\n\n'
def save(name,obj):
 raw=(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode();(HERE/name).write_bytes(raw);return sha(raw)
def load(path,expected):
 with path.open('rb') as f:raw=f.read(MAX+1)
 if sha(raw)!=expected:raise ValueError('input pin '+str(path))
 if path.suffix=='.gz':
  with gzip.GzipFile(fileobj=io.BytesIO(raw)) as z:body=z.read(MAX+1)
 else:body=raw
 return json_raw(body),{'path':str(path),'sha256':sha(raw),'bytes':len(raw),'uncompressed_sha256':sha(body),'uncompressed_bytes':len(body)}
def main():
 pins={
 'CANONICAL-WORD.json.gz':'f1c2ede9276d4447c5857d0e9d32adb52f987b8adb643b45bde2c172d88c6ee9',
 'LOCAL-PROGRAMS.json.gz':'ce194f8465079db575a9ce17ccee1396fa4de0210e2817da2525f95f4f93ebde',
 'CLIFFORD-RECIPES.json':'20dddfce0ded7e41dc507939df7297bd98aec1286e05d7dbf18000d57e69a0b7'}
 loaded={};inputs={}
 for n,h in pins.items():loaded[n],inputs[n]=load(LOCAL/n,h)
 c=loaded['CANONICAL-WORD.json.gz'];programs=loaded['LOCAL-PROGRAMS.json.gz'];recipes=loaded['CLIFFORD-RECIPES.json']
 dims=[]
 for f in arr(c['frames'],1005):
  arr(f)
  for x in f:integer(x,0,512)
  dims.append(len(f))
 starts=arr(c['start'],728)
 for x in starts:frame(x)
 if set(programs)!= {'forward','backward'}:raise ValueError('orientation keys')
 keys=[];keymap={}
 for ordinal,child in enumerate(arr(recipes['children'],2949)[:3]):
  if type(child) is not dict or set(child)!= {'old','new','rank','left','right'}:raise ValueError('child schema')
  a,b,k=frame(child['old']),frame(child['new']),integer(child['rank'],1,10)
  if (a,b) in keymap:raise ValueError('ambiguous directed key')
  keymap[a,b]=(ordinal,k);keys.append([a,b,k])
 if keymap[0,4]!=(2,1):raise ValueError('selected current key')
 rows={};hist={};prefix={};omitted={};supports={}
 for orientation in ('forward','backward'):
  raw=arr(programs[orientation],24399)
  rows[orientation]=[decode_row(i,raw[i],keymap) for i in range(9241,9274)]
  hist[orientation]=dict(collections.Counter(r['event'][0] for r in rows[orientation]))
  prefix[orientation]=dict(collections.Counter(r[0]+(':'+r[1][0] if r[0]=='scalar' else '') for r in raw[:9241]))
  if prefix[orientation]!={'phase':3,'scalar:scale':339,'scalar:add':8171,'adapter':440,'residual_adapter':288}:raise ValueError('pre-A source boundary')
  omitted[orientation]=[{'sourceIndex':i,'row':r} for i,r in enumerate(raw[:9241]) if r[0]!='scalar']
  supports[orientation]=[[r['event'][1] for r in block if r['event'][0]=='relabel'] for block in (rows[orientation][:24],rows[orientation][24:])]
 expected=[[558,572,559,582,560,570,561],[584]]
 if supports!={o:expected for o in rows}:raise ValueError('support order')
 # Explicit exact signed syntax regression. It is source-only and outside the certified33 rows.
 signed=decode_row(1,programs['backward'][1],keymap)
 if signed['event']!=['scale',119,[2,-1]]:raise ValueError('signed regression')
 controls=[]
 for label,fn in [('duplicate_json',lambda:json_raw(b'{"a":1,"a":2}')),('nonfinite',lambda:json_raw(b'{"a":NaN}')),('bool_integer',lambda:integer(True)),('zero_denominator',lambda:coeff(2,0)),('bad_frame',lambda:frame(1005)),('bad_register',lambda:reg(['C',8])),('unknown_row',lambda:decode_row(0,['unknown'],keymap))]:
  try:fn()
  except ValueError:controls.append(label)
  else:raise ValueError('negative accepted '+label)
 lean='''/- Exact selected current799 gauge44 skinny tables and raw9241..9273 in each orientation.
1005 frame dimensions and the first3 of2949 directed child keys retain exact source order.
The bounded catalog prefix includes ordinal2; no full catalog theorem is claimed.
Generated by decode_current33.py. No kernel, operator or omitted-adapter claim. -/
import CanonicalFrameCoverage

set_option Elab.async false
namespace CurrentMain.Current799First33CoverageData
open CurrentMain.CanonicalFrameCoverage
'''
 lean+=emit_array('frameDimensions','Nat',list(map(str,dims)))
 lean+=emit_array('initialOriginalLabels','(FrameLabel 1005)',list(map(str,starts)))
 lean+=emit_array('children','(ChildKey 1005)',['⟨'+', '.join(map(str,k))+'⟩' for k in keys])
 for o in rows:
  for name,block in [('A',rows[o][:24]),('B',rows[o][24:])]:
   lean+=f'def {o}{name} : List (Row 1005) := [\n'+',\n'.join(lean_row(r) for r in block)+'\n]\n\n'
 lean+='''def data : SelectedData 1005 :=
  ⟨frameDimensions, initialOriginalLabels, children, forwardA ++ forwardB, backwardA ++ backwardB⟩
/-- Current canonical entrance labels; this is not a physical frame chart. -/
def labels0 : Register → FrameLabel 1005 := initialLabels 0 data
'''
 for num,support,prev in [(24,expected[0],0),(33,expected[1],24)]:
  lean+=f'def support{num} : List Register := ['+', '.join(map(str,support))+']\n'
  lean+=f'def labels{num} (r : Register) : FrameLabel 1005 :=\n  if r ∈ support{num} then 4 else labels{prev} r\n'
 lean+='end CurrentMain.Current799First33CoverageData\n'
 (HERE/'Current799First33CoverageData.lean').write_text(lean)
 projection={'source_commit':'f567884aeb8851b6e794af1184119a3bfbe1e631','inputs':inputs,'dimensions':dims,'starts':starts,'children':keys,'rows':rows,'raw_rows':{o:programs[o][9241:9274] for o in rows},'supports':supports,'histogram':hist,'pre_A_tag_counts':prefix,'signed_regression':signed,'excluded_note':'Pre-A ADD/SCALE are label-neutral by Event.lab. All omitted phases/adapters remain unproved; no prefix WellLabelled or physical endpoint follows.'}
 ph=save('LITERAL_PROJECTION.json',projection);oh=save('PRE_A_OMITTED_ROWS.json',omitted)
 audit={'status':'STRICT_SOURCE_LITERAL_PROJECTION_ONLY','decoder_sha256':sha(Path(__file__).read_bytes()),'data_source_sha256':sha(lean.encode()),'data_bytes':len(lean.encode()),'inputs':inputs,'projection_sha256':ph,'omitted_sha256':oh,'negative_controls':controls,'rows_each':33,'split':[24,9],'histogram':hist,'source_ready_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-START,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'limits':{'AS':512*1024**2,'CPU':20,'wall':30},'no_upstream_execution':True,'no_label_operator_replay':True}
 print(json.dumps({'audit_sha256':save('DECODER_AUDIT.json',audit),**audit}))
if __name__=='__main__':main()
