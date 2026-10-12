from pathlib import Path
import collections,datetime,hashlib,importlib.util,json,re,subprocess,time
HERE=Path(__file__).resolve().parent;P=HERE.parent
spec=importlib.util.spec_from_file_location('owned_current_decoder',P/'decode_current45.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):p=Path(p);return dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
def save(n,x):p=HERE/n;assert not p.exists();p.write_text(json.dumps(x,indent=2)+'\n');return pin(p)
proposal=json.loads((P/'NEXT_TWO_KEY_BATCH_PROPOSAL.json').read_text());assert sha(P/'NEXT_TWO_KEY_BATCH_PROPOSAL.json')=='202ac8443c68788b09e6bd9ae4cfc634ab83a93b7ab3b528f86479a5ace6205e'
programs,pp=m.load(m.LOCAL/'LOCAL-PROGRAMS.json.gz','d403a1b263a43a40448046c7661919206d222bf37e85b63a4a8950144b8c158f');recipes,rp=m.load(m.LOCAL/'CLIFFORD-RECIPES.json','577a1be13f5140d9c3997637784b2f812f46b24c61877699430b02de4f662102')
keymap={(x['old'],x['new']):(i,x['rank'])for i,x in enumerate(recipes['children'])};assert len(keymap)==2927
blocks=proposal['blocks'];rows={};hist={};rawrows={}
for o in ('forward','backward'):
 rows[o]={};hist[o]={};rawrows[o]={}
 for letter,block in zip('EFGH',blocks):
  lo,hi=block['raw_inclusive'];rs=[m.decode_row(i,programs[o][i],keymap)for i in range(lo,hi+1)];rows[o][letter]=rs;rawrows[o][letter]=programs[o][lo:hi+1]
  h=dict(collections.Counter(r['event'][0]for r in rs));hist[o][letter]=h
  assert [r['event'][1]for r in rs if r['event'][0]=='relabel']==block['support']
  assert all(r['childRef']is None or r['childRef']==[block['child_ordinal'],1]for r in rs)
  assert all(r['event'][2:]==block['directed_key'][:2]for r in []), 'no numerical execution'
  assert all(r['event'][2:]==block['directed_key'][:2]for r in rs if r['event'][0]=='relabel')
  assert h=={'relabel':block['histogram_each']['relabel'],'add':block['histogram_each']['ADD']}
s='''/- Exact current535 two-key source-literal batch raw10781..10870, both orientations.
Keys ordinal2/0→4 and ordinal3/0→5 retain all ordered operands and signed coefficients.
No operator, whole-stream or omitted-adapter conclusion. -/
import Current535Child003Check

set_option Elab.async false
namespace CurrentMain.Current535TwoKeyData
open CurrentMain.CanonicalFrameCoverage
'''
for o in rows:
 for letter in 'EFGH':s+=f'def {o}{letter} : List (Row 997) := [\n'+',\n'.join(m.lean_row(r)for r in rows[o][letter])+'\n]\n\n'
previous='Current535Child003Data.labels90'
for block in blocks:
 end=block['checkpoint'];label=block['directed_key'][1];support=block['support'];s+=f'def support{end} : List Register := ['+', '.join(map(str,support))+']\n';s+=f'def labels{end} (r : Register) : FrameLabel 997 :=\n  if r ∈ support{end} then {label} else {previous} r\n';previous=f'labels{end}'
s+='end CurrentMain.Current535TwoKeyData\n';(HERE/'Current535TwoKeyData.lean').write_text(s)
c='''/- One measured synchronous90-row two-key batch, in four24/21 decisions.
All earlier90 rows are consumed by accepted theorems; no prefix check is replayed.
The conclusion remains current canonical labels/catalog, not operator or full physical execution. -/
import Current535TwoKeyData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current535TwoKeyCheck
open CurrentMain.CanonicalFrameCoverage

''';names=[]
def th(name,text):
 global c
 names.append(name);c+='theorem '+name+' '+text+'\n\n'
for letter,block in zip('EFGH',blocks):
 start=block['raw_inclusive'][0];size=block['rows_each'];th('exact_'+letter+'_source_indices',f':\n    Current535TwoKeyData.forward{letter}.map Row.sourceIndex = List.range\' {start} {size} ∧\n    Current535TwoKeyData.backward{letter}.map Row.sourceIndex = List.range\' {start} {size} := by decide +kernel')
for o in ('forward','backward'):
 prefix=f'(((Current535CoverageData.{o}A ++ Current535CoverageData.{o}B) ++ Current535Child003Data.{o}C) ++ Current535Child003Data.{o}D)'
 previousWL=f'Current535Child003Check.{o}_composed_wellLabelled90';previousCP=f'Current535Child003Check.{o}_composed_checkpoint90';labels='Current535Child003Data.labels90'
 for letter,block in zip('EFGH',blocks):
  end=block['checkpoint'];label=block['directed_key'][1];r=f'Current535TwoKeyData.{o}{letter}';stem=f'{o}_{letter}';support=f'Current535TwoKeyData.support{end}';after=f'Current535TwoKeyData.labels{end}'
  th(stem+'_labels_checked',f':\n    labelRowsB {r} {labels} = true := by decide +kernel')
  th(stem+'_children_checked',f':\n    childRowsB Current535CoverageData.data {r} = true := by decide +kernel')
  th(stem+'_checked',f':\n    checkRows Current535CoverageData.data {r} {labels} = true := by\n  rw [checkRows_factor]\n  exact Bool.and_eq_true_iff.mpr ⟨{stem}_labels_checked, {stem}_children_checked⟩')
  th(stem+'_wellLabelled',f':\n    LemmaG.Stream.WellLabelled ({r}.map Row.event) {labels} :=\n  checkRows_wellLabelled Current535CoverageData.data {r} {labels} {stem}_checked')
  th(f'{o}_support{end}',f':\n    ({r}.map Row.event).all (supportedB {support}) = true := by decide +kernel')
  th(f'{o}_touched{end}',f':\n    {support}.all (fun r =>\n      LemmaG.Stream.labRun ({r}.map Row.event) {labels} r ==\n        ({label} : FrameLabel 997)) = true := by decide +kernel')
  th(f'{o}_checkpoint{end}',f':\n    LemmaG.Stream.labRun ({r}.map Row.event) {labels} = {after} :=\n  sparse_checkpoint {r} {labels} (fun _ => ({label} : FrameLabel 997))\n    {support} {o}_support{end} {o}_touched{end}')
  prefix=f'({prefix} ++ {r})'
  th(f'{o}_composed_wellLabelled{end}',f':\n    LemmaG.Stream.WellLabelled ({prefix}.map Row.event) Current535CoverageData.labels0 := by\n  rw [List.map_append]\n  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr\n  refine ⟨{previousWL}, ?_⟩\n  rw [{previousCP}]\n  exact {stem}_wellLabelled')
  th(f'{o}_composed_checkpoint{end}',f':\n    LemmaG.Stream.labRun ({prefix}.map Row.event) Current535CoverageData.labels0 = {after} := by\n  rw [List.map_append, LemmaG.Stream.labRun_append, {previousCP}]\n  exact {o}_checkpoint{end}')
  previousWL=f'{o}_composed_wellLabelled{end}';previousCP=f'{o}_composed_checkpoint{end}';labels=after
c+='\n'.join('#print axioms '+n for n in names)+'\nend CurrentMain.Current535TwoKeyCheck\n';(HERE/'Current535TwoKeyCheck.lean').write_text(c)
audit=save('LITERAL_PROJECTION.json',{'status':'SOURCE_LITERAL_ONLY','current_snapshot':'7dfa22b109996e48db68daac3706e7a49a43002b','inputs':[pp,rp],'decoder':pin(P/'decode_current45.py'),'generator':pin(__file__),'blocks':blocks,'raw_rows':rawrows,'typed_rows':rows,'histograms':hist,'catalog_records':{str(i):recipes['children'][i]for i in [2,3]},'no_label_or_operator_execution':True})
scanner=P.parent/'f19-label-recipe-coverage-proposal/tools/lean_delimiter_advisory.py';ad=[]
for f in HERE.glob('*.lean'):
 t=time.monotonic();r=subprocess.run(['python3',str(scanner),str(f)],capture_output=True,text=True,check=True);ad.append({'source':pin(f),'result':json.loads(r.stdout),'elapsed_seconds':time.monotonic()-t})
adv=save('DELIMITER_ADVISORY.json',{'helper':pin(scanner),'results':ad,'advisory_only':True})
Q=Path('/workspace/scratch/c569c316cd54/recovery_20261011/post114_reconstruction')
scope=save('SOURCE_SCOPE.json',{'status':'FROZEN_SOURCE_ROOT_RELEASED_8_6_2_PENDING_REVIEWS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'authority':'Root approval relayed by integration2026-10-12T14:42:34UTC: source preparation and one measured8/6/2 first gate after independent science/API/binding. Bank is sole next compiler owner.','next_owner':'/root/prove_main_bank_routing','sources':[pin(HERE/n)for n in ['Current535TwoKeyData.lean','Current535TwoKeyCheck.lean']],'literal_projection':audit,'advisory':adv,'proposal':pin(P/'NEXT_TWO_KEY_BATCH_PROPOSAL.json'),'prior90_acceptance':pin(Q/'bank/current535_child003/ACCEPTANCE.json'),'prior90_terminal':pin(Q/'machine/CURRENT535_COVERAGE90_TERMINAL_INDEPENDENT_REVIEW.json'),'blocks':blocks,'local_scope':{'total':8,'retained':6,'fresh':2},'external_pairs':2213,'new_rows_each':90,'new_histogram_each':{'ADD':62,'relabel':28},'composed_rows_each':180,'composed_histogram_each':{'ADD':124,'relabel':56},'full_label_domain':736,'frame_count':997,'child_count':2927,'new_probe_count':len(names),'resources':proposal['resource_plan'],'baseline':proposal['measured_baselines'],'success':proposal['success'],'limits':proposal['limitations'],'proof_reuse':'Four24/21 factored checks and unchanged sparse_checkpoint API; exact successive whole-label states114/135/159/180. All prefix90 facts retained, no recomputation.','compiler_status':'Unstarted; independent source/API and binding seals required.'})
assert len(names)==76
print(json.dumps(scope));print(json.dumps([pin(HERE/n)for n in ['Current535TwoKeyData.lean','Current535TwoKeyCheck.lean']]))
