#!/usr/bin/env python3
"""Exact bounded slice emission; no supplier, label-admissibility or operator replay."""
from pathlib import Path
import hashlib,importlib.util,json,gzip,time,resource
HERE=Path(__file__).resolve().parent
PILOT=HERE.parents[1]
ROOT=PILOT.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
decoder=PILOT/'decode_pilot.py'
assert sha(decoder)=='89be739f32fecd831140c33f9d85027c6b2d69c17b6efc57e6faed591bc84946'
spec=importlib.util.spec_from_file_location('reviewed_literal_decoder',decoder)
x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)
start=time.monotonic();pins=x.json_raw((PILOT.parent/'SOURCE_PINS.json').read_bytes());inputs={};input_pins=[]
for r in pins['inputs']:
 if r['role']!='decoder input':continue
 p=ROOT/r['path'];assert sha(p)==r['sha256']and p.stat().st_size==r['bytes'];input_pins.append(r)
 if p.suffix=='.gz':
  with gzip.open(p,'rb')as f:b=f.read(x.MAX+1)
 else:b=p.read_bytes()
 inputs[p.name]=x.json_raw(b)
programs=inputs['LOCAL-PROGRAMS.json.gz'];children=inputs['CLIFFORD-RECIPES.json']['children'];lookup={(c['old'],c['new']):(i,c['rank'])for i,c in enumerate(children)};assert len(lookup)==2922
selected={};raw={}
for part,(a,b)in {'A':(11043,11107),'B':(11107,11171)}.items():
 for n in ('forward','backward'):
  key=n+part;raw[key]=programs[n][a:b];selected[key]=[x.decode_row(i,programs[n][i],lookup)for i in range(a,b)]
  assert len(selected[key])==64 and all(r is not None for r in selected[key])
lean='''/- Exact two-slice source data only. Every raw signed coefficient and child ordinal is retained.
The sparse checkpoints are proposals until the separately named full-state equations pass. -/
import F19CoverageNextCheck
namespace CurrentMain.F19SelectedCoverage.BatchData
open CurrentMain.F19SelectedCoverage

def new192 : List Register := [126, 218]
def labels192 (r : Register) : FrameLabel :=
  if r ∈ new192 then 2 else NextData.checkpointLabels r

def new256 : List Register := [216]
def labels256 (r : Register) : FrameLabel :=
  if r ∈ new256 then 2 else labels192 r

'''
for key,rows in selected.items():
 lean+=f'def {key} : List Row := [\n'+',\n'.join(x.lean_row(r)for r in rows)+'\n]\n\n'
lean+='end CurrentMain.F19SelectedCoverage.BatchData\n'
out=HERE/'F19CoverageBatchData.lean';assert not out.exists();out.write_text(lean)
audit={'status':'SOURCE_LITERALS_ONLY','inputs':input_pins,'decoder_sha256':sha(Path(__file__)),'reused_decoder_sha256':sha(decoder),'raw_rows':raw,'typed_rows':selected,'sparse_checkpoints':{'new192':[126,218],'new256':[216],'representation':'Layered sparse overrides of the already accepted full checkpoint; no copied prefix evaluation.'},'data_source_sha256':sha(out),'data_source_bytes':out.stat().st_size,'scope':'Two64-row slices per orientation, original source indices11043..11170, no omitted row. No label predicate evaluated.','elapsed_seconds':time.monotonic()-start,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'limits':{'CPU_seconds':20,'AS_bytes':512*1024**2,'wall_seconds':30},'upstream_execution':False}
(HERE/'BATCH_LITERAL_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n');print(json.dumps({k:audit[k]for k in ('data_source_sha256','data_source_bytes','elapsed_seconds','maxrss_bytes')}))
