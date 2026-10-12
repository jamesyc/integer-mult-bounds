#!/usr/bin/env python3
"""Strict source-literal projection only. Never imports upstream suppliers or evaluates operators."""
from pathlib import Path
import collections, datetime, gzip, hashlib, io, json, resource, time
START=time.monotonic()
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
PINS=HERE.parent/'SOURCE_PINS.json'
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
def frame(x):return integer(x,0,983)
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
 tag=row[0]
 if tag=='phase':
  arr(row,2)
  if row[1] not in ('zero_frame_precondition','entry_adapters','A','centers','B','final','exit_adapters','full_frame_cleanup','done'):raise ValueError('phase')
  return None
 if tag=='adapter':
  arr(row,4)
  if row[1] not in ('old_to_new','new_to_old'):raise ValueError('adapter')
  integer(row[2],0,728);frame(row[3]);return None
 if tag=='residual_adapter':
  arr(row,4)
  if row[1] not in ('pre','post'):raise ValueError('residual')
  integer(row[2],0,728);frame(row[3]);return None
 if tag in ('climb','center'):
  arr(row,6 if tag=='climb' else 5)
  if tag=='climb':
   if row[1] not in ('A','B','final'):raise ValueError('climb part')
   r=integer(row[2],0,728);a,b,k=row[3:]
  else:r=728+integer(row[1],0,8);a,b,k=row[2:]
  frame(a);frame(b);integer(k,1,10)
  if (a,b) not in keymap:raise ValueError('missing directed child')
  ordinal,recordrank=keymap[a,b]
  if recordrank!=k:raise ValueError('directed rank mismatch')
  return {'sourceIndex':i,'event':['relabel',r,a,b],'scalarFrame':None,'childRef':[ordinal,k]}
 if tag!='scalar':raise ValueError('unknown event tag')
 arr(row,3);e=arr(row[1]);f=frame(row[2])
 if not e:raise ValueError('empty scalar')
 op=e[0]
 if op=='add':arr(e,5);event=[op,reg(e[1]),reg(e[2]),coeff(e[3],e[4])]
 elif op=='scale':arr(e,4);event=[op,reg(e[1]),coeff(e[2],e[3])]
 elif op=='copy':arr(e,3);event=[op,reg(e[1]),reg(e[2]),f]
 elif op=='clear':arr(e,2);event=[op,reg(e[1]),f]
 else:raise ValueError('unknown scalar tag')
 return {'sourceIndex':i,'event':event,'scalarFrame':f,'childRef':None}
def lean_row(row):
 e=row['event'];tag=e[0]
 if tag in ('relabel','copy'):event='.'+tag+' '+' '.join(map(str,e[1:]))
 elif tag=='clear':event='.clear '+' '.join(map(str,e[1:]))
 else:event='.'+tag+' '+' '.join(map(str,e[1:-1]))+f' (({e[-1][0]}), ({e[-1][1]}))'
 f='none' if row['scalarFrame'] is None else 'some '+str(row['scalarFrame'])
 ref='none' if row['childRef'] is None else 'some ('+', '.join(map(str,row['childRef']))+')'
 return f'  ⟨{row["sourceIndex"]}, {event}, {f}, {ref}⟩'
def emit_array(name,ty,values):return f'def {name} : Array {ty} := #[\n  '+',\n  '.join(values)+'\n]\n\n'
def save(name,obj):
 raw=(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode();(HERE/name).write_bytes(raw);return sha(raw)
def main():
 pins=json_raw(PINS.read_bytes());inputs={};loaded={}
 for r in pins['inputs']:
  p=ROOT/r['path'];raw=p.read_bytes()
  if len(raw)!=r['bytes'] or sha(raw)!=r['sha256']:raise ValueError('input pin '+str(p))
  if r['role']!='decoder input':continue
  if p.suffix=='.gz':
   with gzip.GzipFile(fileobj=io.BytesIO(raw)) as z:body=z.read(MAX+1)
  else:body=raw
  loaded[p.name]=json_raw(body)
  inputs[p.name]={'path':r['path'],'sha256':sha(raw),'bytes':len(raw),'uncompressed_sha256':sha(body),'uncompressed_bytes':len(body)}
 c=loaded['CANONICAL-WORD.json.gz'];programs=loaded['LOCAL-PROGRAMS.json.gz'];recipes=loaded['CLIFFORD-RECIPES.json']
 frames=arr(c['frames'],983);dims=[]
 for f in frames:
  arr(f)
  for x in f:integer(x,0,512)
  dims.append(len(f))
 start=arr(c['start'],728)
 for x in start:frame(x)
 if set(programs)!= {'forward','backward'}:raise ValueError('orientation keys')
 children=arr(recipes['children'],2922);keys=[];keymap={}
 for ordinal,child in enumerate(children):
  if type(child) is not dict or set(child)!= {'old','new','rank','left','right'}:raise ValueError('child schema')
  a,b,k=frame(child['old']),frame(child['new']),integer(child['rank'],1,10)
  if (a,b) in keymap:raise ValueError('ambiguous directed key')
  keymap[a,b]=(ordinal,k);keys.append([a,b,k])
 decoded={};omitted={};pilot={};prefix={};hist={}
 for orientation in ('forward','backward'):
  rows=arr(programs[orientation],22937);decoded[orientation]=[];omitted[orientation]=[];pilot[orientation]=[]
  hist[orientation]=dict(collections.Counter(row[0] for row in rows))
  for i,row in enumerate(rows):
   item=decode_row(i,row,keymap)
   if item is None:omitted[orientation].append({'sourceIndex':i,'row':row})
   else:decoded[orientation].append(item)
   if 10851<=i<10979:
    if item is None:raise ValueError('pilot contains omitted boundary')
    pilot[orientation].append(item)
  if len(decoded[orientation])!=21320 or len(pilot[orientation])!=128:raise ValueError('projection count')
  prior=[r for r in decoded[orientation] if r['sourceIndex']<10851]
  if any(r['event'][0] not in ('add','scale') for r in prior):raise ValueError('prefix changes canonical labels')
  prefix[orientation]={'raw_range':[0,10851],'retained_count':len(prior),'retained_tags':dict(collections.Counter(r['event'][0] for r in prior)),'label_effect':'PR509 add/scale preserve labels; excluded adapter rows carry no identity-operator claim'}
 signed=decode_row(1,programs['backward'][1],keymap)
 if signed['event']!=['scale',119,[2,-1]]:raise ValueError('signed regression')
 controls=[]
 for label,fn in [
  ('duplicate_json_key',lambda:json_raw(b'{"a":1,"a":2}')),
  ('nonfinite_json',lambda:json_raw(b'{"a":NaN}')),
  ('boolean_integer',lambda:integer(True)),
  ('zero_denominator',lambda:coeff(2,0)),
  ('unknown_event',lambda:decode_row(0,['unknown'],keymap)),
  ('invalid_register',lambda:reg(['C',8])),
  ('wrong_scalar_arity',lambda:decode_row(0,['scalar',['scale',['L',119],2],0],keymap)),
 ]:
  try:fn()
  except ValueError:controls.append(label)
  else:raise ValueError('control accepted '+label)
 # The only Lean data emitted are complete skinny lookup tables and the bounded256 rows.
 lean='''/- Exact f19 source-literal pilot data. Generated by decode_pilot.py under SOURCE_PINS.json.
Only raw rows 10851..10978 in each orientation are retained as events.
No operator, full-stream, or finite-check result is asserted by this data file. -/
import F19CoverageStatement
namespace CurrentMain.F19SelectedCoverage.PilotData
open CurrentMain.F19SelectedCoverage
'''
 lean+=emit_array('frameDimensions','Nat',list(map(str,dims)))
 lean+=emit_array('initialOriginalLabels','FrameLabel',list(map(str,start)))
 lean+=emit_array('children','ChildKey',['⟨'+', '.join(map(str,k))+'⟩' for k in keys])
 for name in ('forward','backward'):
  lean+=f'def {name} : List Row := [\n'+',\n'.join(lean_row(r) for r in pilot[name])+'\n]\n\n'
 lean+='''def data : SelectedData := ⟨frameDimensions, initialOriginalLabels, children, forward, backward⟩
end CurrentMain.F19SelectedCoverage.PilotData
'''
 raw=lean.encode()
 if len(raw)>1024**2:raise ValueError('data source exceeds1MiB')
 (HERE/'F19CoveragePilotData.lean').write_bytes(raw)
 omitted_sha=save('OMITTED_ROWS.json',omitted)
 projection={'pilot_raw_range_inclusive':[10851,10978],'frames_dimensions':dims,'initial_original_labels':start,'directed_children':keys,'pilot_rows':pilot,'raw_pilot_rows':{n:programs[n][10851:10979] for n in programs},'signed_raw_regression':{'raw_row':programs['backward'][1],'decoded':signed}}
 projection_sha=save('LITERAL_PROJECTION.json',projection)
 audit={'status':'SOURCE_LITERAL_DECODING_ONLY_NO_LABEL_OR_OPERATOR_REPLAY','source_pins_sha256':sha(PINS.read_bytes()),'decoder_sha256':sha(Path(__file__).read_bytes()),'inputs':inputs,'program_tag_counts':hist,'pilot_rows_per_orientation':128,'raw_indices_inclusive':[10851,10978],'full_projected_rows_per_orientation':21320,'excluded_boundary_rows_per_orientation':1617,'prefix_label_source_evidence':prefix,'negative_controls_rejected':controls,'signed_denominator_retained':True,'data_source_sha256':sha(raw),'data_source_bytes':len(raw),'literal_projection_sha256':projection_sha,'omitted_rows_sha256':omitted_sha,'max_json_bytes':MAX,'limits':{'address_space_bytes':512*1024**2,'cpu_seconds':20,'external_wall_seconds':30},'observed_elapsed_seconds':time.monotonic()-START,'observed_maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'actions':{'upstream_script_import':False,'generator_replay':False,'operator_or_matrix_replay':False,'lean_compiler':False,'full_label_check':False}}
 print(json.dumps({'audit_sha256':save('DECODER_AUDIT.json',audit),'data_source_sha256':sha(raw),'data_source_bytes':len(raw),'elapsed_seconds':audit['observed_elapsed_seconds'],'maxrss_bytes':audit['observed_maxrss_bytes']}))
if __name__=='__main__':main()
