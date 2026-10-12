#!/usr/bin/env python3
"""Emit only raw11352..11399, split24+24, using the pinned literal decoder."""
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
selected={};raw={};counts={};supports={'K':[676],'L':[454,455,530,531]}
for part,(a,b)in {'K':(11352,11376),'L':(11376,11400)}.items():
 for direction in ('forward','backward'):
  key=direction+part;raw[key]=programs[direction][a:b];selected[key]=[x.decode_row(i,programs[direction][i],lookup)for i in range(a,b)];assert all(r is not None for r in selected[key]);counts[key]=dict(collections.Counter(r['event'][0]for r in selected[key]))
  moves=[r['event']for r in selected[key]if r['event'][0]=='relabel'];assert moves==[['relabel',i,0,7]for i in supports[part]]
  assert all(r['childRef']==[5,1]for r in selected[key]if r['event'][0]=='relabel')
assert sha(HERE.parent/'child5_body/F19CoverageChild5BodyData.lean')=='c1cba8bd1e98e8d7fc297c412dad77ac384025c3d8abab0ad495b4e1fd343568'
assert sha(HERE.parent/'child5_body/F19CoverageChild5BodyCheck.lean')=='4389ba232c598f08bc2d96237d2ea740694e3ccf557bed53483e93a036f4abf2'
lean='''/- Exact selected source rows; checkpoint validity is proved separately.
Raw signed coefficient syntax, order, source indices and child ordinals are retained. -/
import F19CoverageChild5BodyCheck
namespace CurrentMain.F19SelectedCoverage.Child5MoreData
open CurrentMain.F19SelectedCoverage

def new525 : List Register := [676]
def labels525 (r : Register) : FrameLabel :=
  if r ∈ new525 then 7 else Child5BodyData.labels501 r

def new549 : List Register := [454, 455, 530, 531]
def labels549 (r : Register) : FrameLabel :=
  if r ∈ new549 then 7 else labels525 r

'''
for key,rows in selected.items():lean+=f'def {key} : List Row := [\n'+',\n'.join(x.lean_row(r)for r in rows)+'\n]\n\n'
lean+='end CurrentMain.F19SelectedCoverage.Child5MoreData\n';out=HERE/'F19CoverageChild5MoreData.lean';assert not out.exists();out.write_text(lean)
a={'status':'SOURCE_LITERAL_EMISSION_ONLY_NO_FINITE_CHECK','inputs':input_pins,'decoder_sha256':sha(Path(__file__)),'reused_decoder_sha256':sha(decoder),'raw_rows':raw,'typed_rows':selected,'branch_counts':counts,'checkpoint_proposals':{'new525_to7':supports['K'],'new549_to7':supports['L']},'raw_range_inclusive':[11352,11399],'no_omitted_rows_in_this_range':True,'child_key':{'ordinal':5,'old':0,'new':7,'rank':1,'record_normalized_sha256':hashlib.sha256(json.dumps(children[5],sort_keys=True,separators=(',',':')).encode()).hexdigest()},'data_source_sha256':sha(out),'data_source_bytes':out.stat().st_size,'elapsed_seconds':time.monotonic()-start,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'limits':{'CPU_seconds':20,'AS_bytes':512*1024**2,'wall_seconds':30},'upstream_execution':False,'accepted_predicate_replay':False};f=HERE/'LITERAL_AUDIT.json';f.write_text(json.dumps(a,indent=2)+'\n');print(json.dumps({k:a[k]for k in('data_source_sha256','data_source_bytes','elapsed_seconds','maxrss_bytes')}))
