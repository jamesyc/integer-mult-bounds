#!/usr/bin/env python3
"""Emit only raw11308..11351, split24+20, using the pinned literal decoder."""
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
selected={};raw={};counts={};supports={'I':[566,567],'J':[]}
for part,(a,b)in {'I':(11308,11332),'J':(11332,11352)}.items():
 for direction in ('forward','backward'):
  key=direction+part;raw[key]=programs[direction][a:b];selected[key]=[x.decode_row(i,programs[direction][i],lookup)for i in range(a,b)];assert all(r is not None for r in selected[key]);counts[key]=dict(collections.Counter(r['event'][0]for r in selected[key]))
  moves=[r['event']for r in selected[key]if r['event'][0]=='relabel'];assert moves==[['relabel',i,0,7]for i in supports[part]]
  assert all(r['childRef']==[5,1]for r in selected[key]if r['event'][0]=='relabel')
assert sha(HERE.parent/'child5_tail/F19CoverageChild5TailData.lean')=='28616b312ce47c6430de00ed51dce2daa88b8b35e4bec135dd6a6bd22fe09355'
assert sha(HERE.parent/'child5_tail/F19CoverageChild5TailCheck.lean')=='42064af04d86584138ee59001ba319536402109c064a2dafcfc538a8327697f2'
lean='''/- Exact selected source rows; checkpoint validity is proved separately.
Raw signed coefficient syntax, order, source indices and child ordinals are retained. -/
import F19CoverageChild5TailCheck
namespace CurrentMain.F19SelectedCoverage.Child5BodyData
open CurrentMain.F19SelectedCoverage

def new481 : List Register := [566, 567]
def labels481 (r : Register) : FrameLabel :=
  if r ∈ new481 then 7 else Child5TailData.labels457 r

def new501 : List Register := []
def labels501 (r : Register) : FrameLabel :=
  if r ∈ new501 then 7 else labels481 r

'''
for key,rows in selected.items():lean+=f'def {key} : List Row := [\n'+',\n'.join(x.lean_row(r)for r in rows)+'\n]\n\n'
lean+='end CurrentMain.F19SelectedCoverage.Child5BodyData\n';out=HERE/'F19CoverageChild5BodyData.lean';assert not out.exists();out.write_text(lean)
a={'status':'SOURCE_LITERAL_EMISSION_ONLY_NO_FINITE_CHECK','inputs':input_pins,'decoder_sha256':sha(Path(__file__)),'reused_decoder_sha256':sha(decoder),'raw_rows':raw,'typed_rows':selected,'branch_counts':counts,'checkpoint_proposals':{'new481_to7':supports['I'],'new501_to7':supports['J']},'raw_range_inclusive':[11308,11351],'no_omitted_rows_in_this_range':True,'child_key':{'ordinal':5,'old':0,'new':7,'rank':1,'record_normalized_sha256':hashlib.sha256(json.dumps(children[5],sort_keys=True,separators=(',',':')).encode()).hexdigest()},'data_source_sha256':sha(out),'data_source_bytes':out.stat().st_size,'elapsed_seconds':time.monotonic()-start,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'limits':{'CPU_seconds':20,'AS_bytes':512*1024**2,'wall_seconds':30},'upstream_execution':False,'accepted_predicate_replay':False};f=HERE/'LITERAL_AUDIT.json';f.write_text(json.dumps(a,indent=2)+'\n');print(json.dumps({k:a[k]for k in('data_source_sha256','data_source_bytes','elapsed_seconds','maxrss_bytes')}))
