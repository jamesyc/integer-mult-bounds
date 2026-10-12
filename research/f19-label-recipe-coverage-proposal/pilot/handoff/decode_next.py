#!/usr/bin/env python3
"""Emit only a proposed sparse label checkpoint and two exact64-row source slices."""
from pathlib import Path
import hashlib,importlib.util,json,gzip,time,resource
HERE=Path(__file__).resolve().parent
PILOT=HERE.parent
ROOT=PILOT.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
decoder=PILOT/'decode_pilot.py'
assert sha(decoder)=='89be739f32fecd831140c33f9d85027c6b2d69c17b6efc57e6faed591bc84946'
spec=importlib.util.spec_from_file_location('reviewed_literal_decoder',decoder)
x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)
start=time.monotonic()
pins=x.json_raw((PILOT.parent/'SOURCE_PINS.json').read_bytes());inputs={}
for r in pins['inputs']:
 if r['role']!='decoder input':continue
 p=ROOT/r['path'];assert sha(p)==r['sha256']and p.stat().st_size==r['bytes']
 if p.suffix=='.gz':
  with gzip.open(p,'rb')as f:b=f.read(x.MAX+1)
 else:b=p.read_bytes()
 inputs[p.name]=x.json_raw(b)
canonical=inputs['CANONICAL-WORD.json.gz'];programs=inputs['LOCAL-PROGRAMS.json.gz'];children=inputs['CLIFFORD-RECIPES.json']['children']
lookup={(c['old'],c['new']):(i,c['rank'])for i,c in enumerate(children)};assert len(lookup)==2922
projection=x.json_raw((PILOT/'LITERAL_PROJECTION.json').read_bytes());assert sha(PILOT/'LITERAL_PROJECTION.json')=='f8e371d661ec8b3f3eafb389879c5ec881f866448bd50931475ca5c577d3185b'
initial=canonical['start']+[0]*8;states={};selected={}
for n in ('forward','backward'):
 labels=initial.copy()
 for i in range(10851,10979):
  item=x.decode_row(i,programs[n][i],lookup)
  assert item==projection['pilot_rows'][n][i-10851]
  e=item['event']
  if e[0]=='relabel':labels[e[1]]=e[3]
  else:assert e[0]=='add'
 changed=[i for i,v in enumerate(labels)if v!=initial[i]]
 assert len(changed)==41 and all(labels[i]==2 for i in changed)
 states[n]=changed
 selected[n]=[x.decode_row(i,programs[n][i],lookup)for i in range(10979,11043)]
 assert all(r is not None for r in selected[n])
assert states['forward']==states['backward']
lean='''/- Exact source-literal data for a proposed label-state handoff. No new finite result.
The 41-index snapshot is a candidate until both complete labRun equations are checked.
The two64-row lists are raw indices10979..11042 and remain unchecked in this gate. -/
import F19CoveragePilotData
namespace CurrentMain.F19SelectedCoverage.NextData
open CurrentMain.F19SelectedCoverage
'''
lean+='def movedRegisters : List Register := ['+', '.join(map(str,states['forward']))+']\n\n'
lean+='''def checkpointLabels (r : Register) : FrameLabel :=
  if r ∈ movedRegisters then 2 else initialLabels PilotData.data r

'''
for n in ('forward','backward'):
 lean+=f'def {n} : List Row := [\n'+',\n'.join(x.lean_row(r)for r in selected[n])+'\n]\n\n'
lean+='end CurrentMain.F19SelectedCoverage.NextData\n'
(HERE/'F19CoverageNextData.lean').write_text(lean)
audit={'status':'SOURCE_LITERAL_ONLY_BOUNDARY_AND_NEXT_CHECK_NOT_COMPILED','decoder_sha256':sha(Path(__file__)),'reused_decoder_sha256':sha(decoder),'source_pins_sha256':sha(PILOT.parent/'SOURCE_PINS.json'),'accepted_projection_sha256':sha(PILOT/'LITERAL_PROJECTION.json'),'moved_registers':states['forward'],'snapshot_definition':'If index is in41 moved registers then label2 else accepted initial label; arbitrary labels do not assert clean payloads.','next_raw_indices_inclusive':[10979,11042],'raw_rows':{n:programs[n][10979:11043]for n in selected},'typed_rows':selected,'next_branch_counts_each':{'relabel':2,'add':62},'source_data_sha256':sha(HERE/'F19CoverageNextData.lean'),'source_data_bytes':len(lean.encode()),'limits':{'cpu_seconds':20,'AS_bytes':512*1024**2,'external_wall_seconds':30},'elapsed_seconds':time.monotonic()-start,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'upstream_code_executed':False,'scalar_operator_replay':False,'accepted_check_replayed':False,'scope':'Only bounded source literal extraction and sparse label projection. No future64-row predicate is evaluated here.'}
(HERE/'LITERAL_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n');print(json.dumps({'data_sha256':audit['source_data_sha256'],'bytes':audit['source_data_bytes'],'audit_sha256':sha(HERE/'LITERAL_AUDIT.json'),'elapsed_seconds':audit['elapsed_seconds']}))
