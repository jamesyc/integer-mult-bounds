#!/usr/bin/env python3
"""Emit only the exact next24+20 source rows and proposed multivalue sparse states."""
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
selected={};raw={};counts={}
for part,(a,b)in {'C':(11171,11195),'D':(11195,11215)}.items():
 for direction in ('forward','backward'):
  key=direction+part;raw[key]=programs[direction][a:b];selected[key]=[x.decode_row(i,programs[direction][i],lookup)for i in range(a,b)];assert all(r is not None for r in selected[key]);counts[key]=dict(collections.Counter(r['event'][0]for r in selected[key]))
old=x.json_raw((HERE.parent/'scaling_experiment/BATCH_LITERAL_AUDIT.json').read_bytes())
for direction in ('forward','backward'):
 assert [x.decode_row(i,programs[direction][i],lookup)for i in range(11107,11171)]==old['typed_rows'][direction+'B']
 moves=[r['event']for r in old['typed_rows'][direction+'B']if r['event'][0]=='relabel'];assert moves==[['relabel',i,0,3]for i in[504,505,528,529]]+[['relabel',i,0,4]for i in[492,493,516,517]]
 assert [r['event']for r in selected[direction+'C']if r['event'][0]=='relabel']==[['relabel',i,0,5]for i in[502,503,514,515]]
 assert [r['event']for r in selected[direction+'D']if r['event'][0]=='relabel']==[['relabel',i,0,6]for i in[490,491,526,527]]
lean='''/- Exact source data only; sparse label functions require the separately proved full handoffs.
Raw signed coefficients, direction, order, source indices and child ordinals are unchanged. -/
import F19CoverageChunkBSplit
namespace CurrentMain.F19SelectedCoverage.Child34Data
open CurrentMain.F19SelectedCoverage

def to3 : List Register := [504, 505, 528, 529]
def to4 : List Register := [492, 493, 516, 517]
def new320 : List Register := to3 ++ to4
def values320 (r : Register) : FrameLabel := if r ∈ to3 then 3 else 4
def labels320 (r : Register) : FrameLabel :=
  if r ∈ new320 then values320 r else BatchData.labels256 r

def new344 : List Register := [502, 503, 514, 515]
def labels344 (r : Register) : FrameLabel :=
  if r ∈ new344 then 5 else labels320 r

def new364 : List Register := [490, 491, 526, 527]
def labels364 (r : Register) : FrameLabel :=
  if r ∈ new364 then 6 else labels344 r

'''
for key,rows in selected.items():lean+=f'def {key} : List Row := [\n'+',\n'.join(x.lean_row(r)for r in rows)+'\n]\n\n'
lean+='end CurrentMain.F19SelectedCoverage.Child34Data\n';out=HERE/'F19CoverageChild34Data.lean';assert not out.exists();out.write_text(lean)
a={'status':'SOURCE_LITERAL_EMISSION_ONLY_NO_FINITE_CHECK','inputs':input_pins,'decoder_sha256':sha(Path(__file__)),'reused_decoder_sha256':sha(decoder),'prior_B_literal_audit_sha256':sha(HERE.parent/'scaling_experiment/BATCH_LITERAL_AUDIT.json'),'raw_rows':raw,'typed_rows':selected,'branch_counts':counts,'checkpoint_proposals':{'new320_to3':[504,505,528,529],'new320_to4':[492,493,516,517],'new344_to5':[502,503,514,515],'new364_to6':[490,491,526,527]},'raw_range_inclusive':[11171,11214],'no_omitted_rows_in_this_range':True,'child_keys':{'3':[0,5,1],'4':[0,6,1]},'data_source_sha256':sha(out),'data_source_bytes':out.stat().st_size,'elapsed_seconds':time.monotonic()-start,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'limits':{'CPU_seconds':20,'AS_bytes':512*1024**2,'wall_seconds':30},'upstream_execution':False,'accepted_predicate_replay':False};f=HERE/'LITERAL_AUDIT.json';f.write_text(json.dumps(a,indent=2)+'\n');print(json.dumps({k:a[k]for k in('data_source_sha256','data_source_bytes','elapsed_seconds','maxrss_bytes')}))
