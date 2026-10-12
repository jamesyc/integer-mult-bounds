#!/usr/bin/env python3
"""Emit only raw11400..11545, split24+24+24+24+24+26, using the pinned literal decoder."""
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
selected={};raw={};counts={};chunks={'M':(11400,11424),'N':(11424,11448),'O':(11448,11472),'P':(11472,11496),'Q':(11496,11520),'R':(11520,11546)}
for part,(a,b)in chunks.items():
 for direction in ('forward','backward'):
  key=direction+part;raw[key]=programs[direction][a:b];selected[key]=[x.decode_row(i,programs[direction][i],lookup)for i in range(a,b)];assert all(r is not None for r in selected[key]);counts[key]=dict(collections.Counter(r['event'][0]for r in selected[key]))
  assert counts[key]=={'add':b-a}
  assert all(r['childRef']is None and r['scalarFrame']==7 for r in selected[key])
assert sha(HERE.parent/'child5_more/F19CoverageChild5MoreData.lean')=='c5fc3ebcc79d397359ac4841b3413453742051dc6b80275a86895f5196f88d7b'
assert sha(HERE.parent/'child5_more/F19CoverageChild5MoreCheck.lean')=='ba2a3a9b9a1457c175222533bfae6104a0efc0669ded9d949f31120b905fedc8'
lean='/- Exact selected static-label rows; checkpoint validity is proved separately.\nRaw signed coefficients and original indices/order are retained. All rows are ADD;\nchild lookup is vacuous in this packet. No scalar/operator endpoint is asserted. -/\nimport F19CoverageChild5MoreCheck\nnamespace CurrentMain.F19SelectedCoverage.StaticGapData\nopen CurrentMain.F19SelectedCoverage\n\n'
prev='Child5MoreData.labels549'
for n in (573,597,621,645,669,695):
 lean+=f'def new{n} : List Register := []\ndef labels{n} (r : Register) : FrameLabel :=\n  if r ∈ new{n} then 7 else {prev} r\n\n'
 prev=f'labels{n}'
for key,rows in selected.items():lean+=f'def {key} : List Row := [\n'+',\n'.join(x.lean_row(r)for r in rows)+'\n]\n\n'
lean+='end CurrentMain.F19SelectedCoverage.StaticGapData\n';out=HERE/'F19CoverageStaticGapData.lean';assert not out.exists();out.write_text(lean)
a={'status':'SOURCE_LITERAL_EMISSION_ONLY_NO_FINITE_CHECK','inputs':input_pins,'decoder_sha256':sha(Path(__file__)),'reused_decoder_sha256':sha(decoder),'raw_rows':raw,'typed_rows':selected,'branch_counts':counts,'checkpoint_proposals':{f'new{n}':[]for n in(573,597,621,645,669,695)},'raw_range_inclusive':[11400,11545],'chunks_half_open':chunks,'no_omitted_rows_in_this_range':True,'child_check_vacuous':True,'data_source_sha256':sha(out),'data_source_bytes':out.stat().st_size,'elapsed_seconds':time.monotonic()-start,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'limits':{'CPU_seconds':20,'AS_bytes':512*1024**2,'wall_seconds':30},'upstream_execution':False,'accepted_predicate_replay':False};f=HERE/'LITERAL_AUDIT.json';f.write_text(json.dumps(a,indent=2)+'\n');print(json.dumps({k:a[k]for k in('data_source_sha256','data_source_bytes','elapsed_seconds','maxrss_bytes')}))
