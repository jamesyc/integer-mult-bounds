#!/usr/bin/env python3
"""Emit only raw11215..11259, split24+21, using the pinned literal decoder."""
from pathlib import Path
import hashlib,importlib.util,json,gzip,time,resource,collections
HERE=Path(__file__).resolve().parent;PILOT=HERE.parents[1];ROOT=PILOT.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
decoder=PILOT/'decode_pilot.py';assert sha(decoder)=='89be739f32fecd831140c33f9d85027c6b2d69c17b6efc57e6faed591bc84946'
spec=importlib.util.spec_from_file_location('reviewed_literal_decoder',decoder);x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)
start=time.monotonic();pins=x.json_raw((PILOT.parent/'SOURCE_PINS.json').read_bytes());inputs={};input_pins=[]
for r in pins['inputs']:
 if r['role']!='decoder input':continue
 p=ROOT/r['path'];assert sha(p)==r['sha256']and p.stat().st_size==r['bytes'];input_pins.append(r)
 if p.suffix=='.gz':
  with gzip.open(p,'rb')as f:b=f.read(x.MAX+1)
 else:b=p.read_bytes()
 inputs[p.name]=x.json_raw(b)
programs=inputs['LOCAL-PROGRAMS.json.gz'];children=inputs['CLIFFORD-RECIPES.json']['children'];lookup={(c['old'],c['new']):(i,c['rank'])for i,c in enumerate(children)};assert len(lookup)==2922
selected={};raw={};counts={};supports={'E':[512,513,522,510,511,524,560,561,570,558,559,572],'F':[582,584]}
for part,(a,b)in {'E':(11215,11239),'F':(11239,11260)}.items():
 for direction in ('forward','backward'):
  key=direction+part;raw[key]=programs[direction][a:b];selected[key]=[x.decode_row(i,programs[direction][i],lookup)for i in range(a,b)];assert all(r is not None for r in selected[key]);counts[key]=dict(collections.Counter(r['event'][0]for r in selected[key]))
  moves=[r['event']for r in selected[key]if r['event'][0]=='relabel'];assert moves==[['relabel',i,0,7]for i in supports[part]]
  assert all(r['childRef']==[5,1]for r in selected[key]if r['event'][0]=='relabel')
assert sha(HERE.parent/'child34/F19CoverageChild34Data.lean')=='6a7e9a15b926f1eaf9f4833877da7b6e1e2914d22cb78c62913455fa037fbd91'
assert sha(HERE.parent/'child34/F19CoverageChild34Check.lean')=='fd7e1029987a5ce70f1c68b25863412bd2f159b14e4639d2217f004609ae35a3'
lean='''/- Exact selected source rows; checkpoint validity is proved separately.
Raw signed coefficient syntax, order, source indices and child ordinals are retained. -/
import F19CoverageChild34Check
namespace CurrentMain.F19SelectedCoverage.Child5Data
open CurrentMain.F19SelectedCoverage

def new388 : List Register := [512, 513, 522, 510, 511, 524, 560, 561, 570, 558, 559, 572]
def labels388 (r : Register) : FrameLabel :=
  if r ∈ new388 then 7 else Child34Data.labels364 r

def new409 : List Register := [582, 584]
def labels409 (r : Register) : FrameLabel :=
  if r ∈ new409 then 7 else labels388 r

'''
for key,rows in selected.items():lean+=f'def {key} : List Row := [\n'+',\n'.join(x.lean_row(r)for r in rows)+'\n]\n\n'
lean+='end CurrentMain.F19SelectedCoverage.Child5Data\n';out=HERE/'F19CoverageChild5Data.lean';assert not out.exists();out.write_text(lean)
a={'status':'SOURCE_LITERAL_EMISSION_ONLY_NO_FINITE_CHECK','inputs':input_pins,'decoder_sha256':sha(Path(__file__)),'reused_decoder_sha256':sha(decoder),'raw_rows':raw,'typed_rows':selected,'branch_counts':counts,'checkpoint_proposals':{'new388_to7':supports['E'],'new409_to7':supports['F']},'raw_range_inclusive':[11215,11259],'no_omitted_rows_in_this_range':True,'child_key':{'ordinal':5,'old':0,'new':7,'rank':1,'record_normalized_sha256':hashlib.sha256(json.dumps(children[5],sort_keys=True,separators=(',',':')).encode()).hexdigest()},'data_source_sha256':sha(out),'data_source_bytes':out.stat().st_size,'elapsed_seconds':time.monotonic()-start,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'limits':{'CPU_seconds':20,'AS_bytes':512*1024**2,'wall_seconds':30},'upstream_execution':False,'accepted_predicate_replay':False};f=HERE/'LITERAL_AUDIT.json';f.write_text(json.dumps(a,indent=2)+'\n');print(json.dumps({k:a[k]for k in('data_source_sha256','data_source_bytes','elapsed_seconds','maxrss_bytes')}))
