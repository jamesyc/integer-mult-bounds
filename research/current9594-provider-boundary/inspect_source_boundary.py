"""Read-only selected-source inventory. Does not import or execute supplier code."""
import collections, datetime, gzip, hashlib, json, pathlib
R=pathlib.Path('/workspace/shared/integer-mult-git/checks/main-9594b61-readback')
OUT=pathlib.Path(__file__).resolve().parent
P='research/complex-571-free4fc8/'
S='research/complex-multicold/'
F=S+'vendor/pr558/vendor/pr552/'
V=F+'complex-global/vendor531/'
GK=F+'complex-local/static44/gk/'
def sha(b):return hashlib.sha256(b).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:
  if k in d:raise ValueError('duplicate key: '+k)
  d[k]=v
 return d
def read(rel):
 p=R/rel
 with p.open('rb')as f:b=f.read(32*1024*1024+1)
 assert len(b)<=32*1024*1024
 if rel.endswith('.gz'):
  with gzip.open(p,'rb')as f:b=f.read(32*1024*1024+1)
  assert len(b)<=32*1024*1024
 return json.loads(b,object_pairs_hook=unique,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def pin(rel):
 b=(R/rel).read_bytes();return dict(path=rel,sha256=sha(b),bytes=len(b))
def save(name,obj):
 p=OUT/name;p.write_text(json.dumps(obj,indent=2)+'\n');print(name,sha(p.read_bytes()),p.stat().st_size)
selected=read('research/community-family588-audit/SELECTED-SOURCE.json')['files']
spec=read(P+'data/SPEC.json');plan=read(P+'data/PLAN.json');roles=read(P+'data/OWNERS.json.gz')
source_paths=[P+x for x in ['MANIFEST.json','NOTICE.md','data/SPEC.json','data/PLAN.json','data/OWNERS.json.gz','code/witness.py','verify.py','code/emit_allcold.py','code/audit_allcold.py','code/bind_providers_portable.py','code/generated_identity.py']]
generation_paths=[S+'code/run_portable.py',S+'code/build_multicut_kernels.py',GK+'gk_word.py',GK+'gk_common.py','research/kernel-frame-coalescing/code/build_frames.py',P+'code/build_gate_moves.py',V+'code/audit_and_transport.py',V+'code/emit_local.py',S+'vendor/pr558/code/phases_full.py',V+'vendor/clifford/clifford_exact.py','research/structural-gain/frontier-composition/combined-prefix-word/FULL-WORD.json.gz',F+'complex-local/inputs/phase-baseline/CANONICAL-WORD.json.gz']+[P+'data/recipes/'+x for x in ['ck-step0-greedy_kernels.json','ck-step1-frame_coalesce.json','ck-step2-gate_move_coalesce.json']]
for rel in source_paths+generation_paths:
 assert selected[rel]==pin(rel)['sha256'],rel
order=[tuple(x)for x in plan['order']];dispatch={(s,r):pid for s,r,pid in spec['dispatch']}
assert len(order)==len(set(order))==72 and set(order)=={(s,r)for s in range(9)for r in range(8)}
assert plan['order']==spec['call_order'] and order==sorted(order,key=lambda x:(7*x[0]+6*x[1],*x))
assert [(x['stage'],x['replica'],x['provider'])for x in plan['provider_calls']]==[tuple(x)for x in spec['dispatch']]
assert sha((R/(P+'data/PLAN.json')).read_bytes())==spec['data']['plan_sha256']
assert sha((R/(P+'data/OWNERS.json.gz')).read_bytes())==spec['data']['owners_sha256']==plan['assignment_sha256']==plan['source_owners_sha256']
groups=collections.defaultdict(list)
for row in roles:groups[row['stage'],row['replica']].append(row)
assert set(groups)==set(order) and len(roles)==36288
for call,rr in groups.items():
 assert len(rr)==504 and {x['helper']for x in rr}==set(range(504))
 assert len({x['family']for x in rr})==504
 for x in rr:
  assert 0<=x['family']<7168
  assert (x['owner_replica'],x['port'])==divmod(x['copy'],112)
  assert x['family']==x['owner_replica']*896+(2*plan['pairs'][str(x['child'])]+plan['sides'][str(x['child'])])*112+x['port']
  assert x['time']==order.index(call)
  assert x['time'] in plan['windows'][f"{x['owner_replica']},{x['child']}"][1]
  assert x['width']==plan['provider_registry'][dispatch[call]]['widths'][x['helper']]
  assert x['offset']>=0 and x['offset']+x['width']<=plan['windows'][f"{x['owner_replica']},{x['child']}"][0]
old=[]
for name in ['LOCAL-PROGRAMS.json.gz','CANONICAL-WORD.json.gz','CLIFFORD-RECIPES.json']:
 rel='research/post-center-rank4-global/evidence/local/'+name
 p=pin(rel);prior=pathlib.Path('/workspace/shared/integer-mult-git/checks/main-7dfa22b-readback')/rel
 assert prior.read_bytes()==(R/rel).read_bytes()
 p['unchanged_from_7dfa']=True;p['selected_manifest_member']=rel in selected;old.append(p)
providers={}
for pid,v in spec['providers'].items():
 providers[pid]={'calls':[list(x)for x in order if dispatch[x]==pid],'count':sum(x==pid for x in dispatch.values()),'expected_events_each':{k:c['events']for k,c in v['complete_contract']['local'].items()},'program_orientation_sha256':v['program_hashes'],'artifact_raw_sha256':plan['provider_registry'][pid]['artifact_sha256'],'artifact_semantic_sha256':v['artifact_semantic_sha256'],'width_inventory':v['inventory'],'build':spec['build']['providers'][pid]}
assembly_rel='research/community-family588-audit/pr588/public-cold/complex/ASSEMBLY.json';assembly=read(assembly_rel)
report={'status':'READ_ONLY_SELECTED_ROUTING_AND_GENERATION_BOUNDARY','completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'head':'9594b61042164a27a31e44d8c3197f231470eda0','selected_manifest':pin('research/community-family588-audit/SELECTED-SOURCE.json'),'source_pins':[pin(x)for x in source_paths],'assembly':pin(assembly_rel),'conditional_kappa':assembly['kappa'],'conditional_kappa_decimal':assembly['kappa_decimal'],'assembly_scope':assembly['scope'],'dispatch':{'counts':dict(collections.Counter(dispatch.values())),'order_rule':'ascending (7*stage+6*replica,stage,replica)','non_ck_calls':[x for x in spec['dispatch']if x[2]!='ck'],'plan_spec_exact_order_match':True,'complete_call_count':72},'owners':{'literal_rows':len(roles),'helpers_per_call':504,'literal_helper_family_distinct_per_call':True,'family_range':[0,7168],'all_time_width_family_and_declared_window_fields_match':True,'cross_replica_rows':sum(x['replica']!=x['owner_replica']for x in roles),'not_proved':['Disjointness from each call active data families requires generated parent call maps.','Declared PLAN windows still need actual complete controller/source-event timing binding.','Orthogonal 73-column sigma, residual/spectator operator and completed arbitrary-dirty endpoint remain separate.']},'provider_records':providers,'old_artifacts':old,'reusable':['Parameterized CanonicalFrameCoverage, checked scalar decoder, sparse checkpoints and list composition unchanged as generic APIs.','PR509 event-restricted RecipesExact and PR516 full-state endpoint contracts remain applicable with actual new suppliers.','Old artifacts and accepted 212-row/first45 proofs stay exact source-specific evidence; no provider literal equivalence is inferred.'],'changed_obligations':['Three provider-local generated catalogs/canonical/programs differ from old selected artifact hashes.','Whole-call provider dispatch, per-provider wrappers/initial frames and owner-family chart binding.','Exact event keys/indices/labels and literal owner windows require current generated artifacts; no ordinal transfer.'],'source_lines':{'witness.py':'6-13: SPEC-derived dispatch/order/provider IDs','emit_allcold.py':'25-79: source pins/provider registry/owner routes; 104-131: whole-call schedule and provider dispatch','audit_allcold.py':'85-118: chronological controller projection; 120-159: actual windows/owner routing/nonalias','verify.py':'59-62: full baseline default; 176-215: provider construction/localization and locals stopping point'},'next_minimum':'Recover exact ck generated artifacts, or generate the single ck chain under a separately reviewed bounded client; then compare literal labels/recipe keys and choose a real current slice.','execution':'No upstream module imported; no supplier, emitter, compiler or scientific replay executed. Static JSON/gzip/hash checks only.'}
save('SOURCE_ROUTING_READBACK.json',report)
save('CK_GENERATION_INPUTS.json',{'head':report['head'],'selected_manifest':report['selected_manifest'],'files':[pin(x)for x in generation_paths],'external_dependencies':'Python 3.13 standard library only; gk_word→gk_common and phases_full→clifford_exact are explicitly listed. Source import search paths must resolve these exact bytes.','root_source_pins':[pin(P+'data/SPEC.json'),pin(P+'verify.py'),pin(P+'code/generated_identity.py')],'source_attribution':[pin(P+'NOTICE.md'),pin(S+'NOTICE.md'),pin('research/kernel-frame-coalescing/NOTICE.md')]})
