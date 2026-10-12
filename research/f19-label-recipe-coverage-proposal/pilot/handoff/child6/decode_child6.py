#!/usr/bin/env python3
"""Emit only raw11546..11593, split24+24, using the pinned literal decoder."""
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
selected={};raw={};counts={};supports={'S':[488,489,498,486,487,500,536,537,546,534,535,548],'T':[586,588,656,657]}
for part,(a,b)in {'S':(11546,11570),'T':(11570,11594)}.items():
 for direction in ('forward','backward'):
  key=direction+part;raw[key]=programs[direction][a:b];selected[key]=[x.decode_row(i,programs[direction][i],lookup)for i in range(a,b)];assert all(r is not None for r in selected[key]);counts[key]=dict(collections.Counter(r['event'][0]for r in selected[key]))
  moves=[r['event']for r in selected[key]if r['event'][0]=='relabel'];assert moves==[['relabel',i,0,8]for i in supports[part]]
  assert all(r['childRef']==[6,1]for r in selected[key]if r['event'][0]=='relabel')
assert sha(HERE.parent/'static_gap/F19CoverageStaticGapData.lean')=='a17529ecfa6d8db49505e0a87354591ad574e0439008c9b8100d525d9d04b11c'
assert sha(HERE.parent/'static_gap/F19CoverageStaticGapCheckB.lean')=='d3a85a31fe9da1d67e651beb8d88490fd72182d34a69152ce4885503f6a1c672'
lean='''/- Exact selected source rows; checkpoint validity is proved separately.
Raw signed coefficient syntax, order, source indices and child ordinals are retained. -/
import F19CoverageStaticGapCheckB
namespace CurrentMain.F19SelectedCoverage.Child6Data
open CurrentMain.F19SelectedCoverage

def new719 : List Register := [488, 489, 498, 486, 487, 500, 536, 537, 546, 534, 535, 548]
def labels719 (r : Register) : FrameLabel :=
  if r ∈ new719 then 8 else StaticGapData.labels695 r

def new743 : List Register := [586, 588, 656, 657]
def labels743 (r : Register) : FrameLabel :=
  if r ∈ new743 then 8 else labels719 r

'''
for key,rows in selected.items():lean+=f'def {key} : List Row := [\n'+',\n'.join(x.lean_row(r)for r in rows)+'\n]\n\n'
lean+='end CurrentMain.F19SelectedCoverage.Child6Data\n';out=HERE/'F19CoverageChild6Data.lean';assert not out.exists();out.write_text(lean)
a={'status':'SOURCE_LITERAL_EMISSION_ONLY_NO_FINITE_CHECK','inputs':input_pins,'decoder_sha256':sha(Path(__file__)),'reused_decoder_sha256':sha(decoder),'raw_rows':raw,'typed_rows':selected,'branch_counts':counts,'checkpoint_proposals':{'new719_to8':supports['S'],'new743_to8':supports['T']},'raw_range_inclusive':[11546,11593],'no_omitted_rows_in_this_range':True,'child_key':{'ordinal':6,'old':0,'new':8,'rank':1,'record_normalized_sha256':hashlib.sha256(json.dumps(children[6],sort_keys=True,separators=(',',':')).encode()).hexdigest()},'data_source_sha256':sha(out),'data_source_bytes':out.stat().st_size,'elapsed_seconds':time.monotonic()-start,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'limits':{'CPU_seconds':20,'AS_bytes':512*1024**2,'wall_seconds':30},'upstream_execution':False,'accepted_predicate_replay':False};f=HERE/'LITERAL_AUDIT.json';f.write_text(json.dumps(a,indent=2)+'\n');print(json.dumps({k:a[k]for k in('data_source_sha256','data_source_bytes','elapsed_seconds','maxrss_bytes')}))
