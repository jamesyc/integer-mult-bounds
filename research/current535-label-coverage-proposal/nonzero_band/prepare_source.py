from pathlib import Path
import collections,datetime,hashlib,importlib.util,json,subprocess,time
HERE=Path(__file__).resolve().parent;P=HERE.parent
spec=importlib.util.spec_from_file_location('owned_current_decoder',P/'decode_current45.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):p=Path(p);return dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
def save(n,x):p=HERE/n;assert not p.exists();p.write_text(json.dumps(x,indent=2)+'\n');return pin(p)
programs,pp=m.load(m.LOCAL/'LOCAL-PROGRAMS.json.gz','d403a1b263a43a40448046c7661919206d222bf37e85b63a4a8950144b8c158f');recipes,rp=m.load(m.LOCAL/'CLIFFORD-RECIPES.json','577a1be13f5140d9c3997637784b2f812f46b24c61877699430b02de4f662102');word,wp=m.load(m.LOCAL/'CANONICAL-WORD.json.gz','e070ae2c78b4a1b644b418774af62b40d8d16e6ba89602f0474afb557d507c37')
keymap={(x['old'],x['new']):(i,x['rank'])for i,x in enumerate(recipes['children'])};assert len(keymap)==len(recipes['children'])==2927
blocks=[dict(letter='K',raw_inclusive=[10903,10926],rows_each=24,checkpoint=236,values=[[0,14],[27,14],[224,15],[57,15],[225,16],[7,16],[76,17],[87,17],[226,18],[92,18],[227,19],[81,19]]),dict(letter='L',raw_inclusive=[10927,10950],rows_each=24,checkpoint=260,values=[[228,20],[232,20],[229,21],[238,21],[230,22],[234,22],[231,23],[236,23],[233,24],[239,24],[235,25],[237,25]])]
for b in blocks:
 b['support']=[r for r,v in b['values']];b['histogram_each']={'ADD':12,'relabel':12}
 b['ordered_keys']=[[row[3],row[4],row[5]]for row in programs['forward'][b['raw_inclusive'][0]:b['raw_inclusive'][1]+1]if row[0]=='climb'];b['child_ordinals']=[keymap[a,z][0]for a,z,rank in b['ordered_keys']]
assert sorted(b for block in blocks for b in block['child_ordinals'])==list(range(253,277))
rows={};rawrows={};hist={}
for o in ('forward','backward'):
 rows[o]={};rawrows[o]={};hist[o]={}
 for b in blocks:
  letter=b['letter'];lo,hi=b['raw_inclusive'];rs=[m.decode_row(i,programs[o][i],keymap)for i in range(lo,hi+1)];rows[o][letter]=rs;rawrows[o][letter]=programs[o][lo:hi+1]
  rel=[r for r in rs if r['event'][0]=='relabel'];assert [r['event'][1]for r in rel]==b['support'];assert [[r['event'][1],r['event'][3]]for r in rel]==b['values'];assert [[r['event'][2],r['event'][3],r['childRef'][1]]for r in rel]==b['ordered_keys'];assert all(6<=r['event'][2]<=13 and 14<=r['event'][3]<=25 and r['childRef']==list(keymap[r['event'][2],r['event'][3]])and r['childRef'][1]==1 for r in rel)
  h=dict(collections.Counter(r['event'][0]for r in rs));assert h=={'relabel':b['histogram_each']['relabel'],'add':b['histogram_each']['ADD']};hist[o][letter]=h
 assert programs[o][10951][:2]==['climb','A']and programs[o][10951][3]==23 and programs[o][10951][4]==26
s='''/- Exact pinned7dfa current535 nonzero-old-frame band raw10903..10950, both orientations.
Twenty-four ordered rank1 children253…276; old6…13 to new14…25.
No operator, omitted-adapter or full physical execution conclusion. -/
import Current535EntranceBandCheck

set_option Elab.async false
namespace CurrentMain.Current535NonzeroBandData
open CurrentMain.CanonicalFrameCoverage
'''
for o in rows:
 for b in blocks:
  letter=b['letter'];s+=f'def {o}{letter} : List (Row 997) := [\n'+',\n'.join(m.lean_row(r)for r in rows[o][letter])+'\n]\n\n'
previous='Current535EntranceBandData.labels212'
for b in blocks:
 end=b['checkpoint'];s+=f'def support{end} : List Register := ['+', '.join(map(str,b['support']))+']\n';s+=f'def values{end} (r : Register) : FrameLabel 997 :=\n  match r.val with\n'+''.join(f'  | {r} => {v}\n'for r,v in b['values'])+'  | _ => 0\n';s+=f'def labels{end} (r : Register) : FrameLabel 997 :=\n  if r ∈ support{end} then values{end} r else {previous} r\n';previous=f'labels{end}'
s+='end CurrentMain.Current535NonzeroBandData\n';assert not (HERE/'Current535NonzeroBandData.lean').exists();(HERE/'Current535NonzeroBandData.lean').write_text(s)
c='''/- Two24+24 factored decisions with multivalue whole-register sparse handoffs.
The accepted212-row prefix is reused by append and checkpoint theorems.
Only label/catalog coverage; all new operator suppliers are separate. -/
import Current535NonzeroBandData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current535NonzeroBandCheck
open CurrentMain.CanonicalFrameCoverage

''';names=[]
def th(name,text):
 global c
 names.append(name);c+='theorem '+name+' '+text+'\n\n'
for b in blocks:
 letter=b['letter'];start=b['raw_inclusive'][0];size=b['rows_each'];th('exact_'+letter+'_source_indices',f':\n    Current535NonzeroBandData.forward{letter}.map Row.sourceIndex = List.range\' {start} {size} ∧\n    Current535NonzeroBandData.backward{letter}.map Row.sourceIndex = List.range\' {start} {size} := by decide +kernel')
for o in ('forward','backward'):
 prefix=f'(Current535CoverageData.{o}A ++ Current535CoverageData.{o}B)'
 for ns,letters in [('Current535Child003Data','CD'),('Current535TwoKeyData','EFGH'),('Current535EntranceBandData','IJ')]:
  for letter in letters:prefix=f'({prefix} ++ {ns}.{o}{letter})'
 previousWL=f'Current535EntranceBandCheck.{o}_composed_wellLabelled212';previousCP=f'Current535EntranceBandCheck.{o}_composed_checkpoint212';labels='Current535EntranceBandData.labels212'
 for b in blocks:
  letter=b['letter'];end=b['checkpoint'];r=f'Current535NonzeroBandData.{o}{letter}';stem=f'{o}_{letter}';support=f'Current535NonzeroBandData.support{end}';values=f'Current535NonzeroBandData.values{end}';after=f'Current535NonzeroBandData.labels{end}'
  th(stem+'_labels_checked',f':\n    labelRowsB {r} {labels} = true := by decide +kernel')
  th(stem+'_children_checked',f':\n    childRowsB Current535CoverageData.data {r} = true := by decide +kernel')
  th(stem+'_checked',f':\n    checkRows Current535CoverageData.data {r} {labels} = true := by\n  rw [checkRows_factor]\n  exact Bool.and_eq_true_iff.mpr ⟨{stem}_labels_checked, {stem}_children_checked⟩')
  th(stem+'_wellLabelled',f':\n    LemmaG.Stream.WellLabelled ({r}.map Row.event) {labels} :=\n  checkRows_wellLabelled Current535CoverageData.data {r} {labels} {stem}_checked')
  th(f'{o}_support{end}',f':\n    ({r}.map Row.event).all (supportedB {support}) = true := by decide +kernel')
  th(f'{o}_touched{end}',f':\n    {support}.all (fun r =>\n      LemmaG.Stream.labRun ({r}.map Row.event) {labels} r == {values} r) = true := by decide +kernel')
  th(f'{o}_checkpoint{end}',f':\n    LemmaG.Stream.labRun ({r}.map Row.event) {labels} = {after} :=\n  sparse_checkpoint {r} {labels} {values}\n    {support} {o}_support{end} {o}_touched{end}')
  prefix=f'({prefix} ++ {r})'
  th(f'{o}_composed_wellLabelled{end}',f':\n    LemmaG.Stream.WellLabelled ({prefix}.map Row.event) Current535CoverageData.labels0 := by\n  rw [List.map_append]\n  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr\n  refine ⟨{previousWL}, ?_⟩\n  rw [{previousCP}]\n  exact {stem}_wellLabelled')
  th(f'{o}_composed_checkpoint{end}',f':\n    LemmaG.Stream.labRun ({prefix}.map Row.event) Current535CoverageData.labels0 = {after} := by\n  rw [List.map_append, LemmaG.Stream.labRun_append, {previousCP}]\n  exact {o}_checkpoint{end}')
  previousWL=f'{o}_composed_wellLabelled{end}';previousCP=f'{o}_composed_checkpoint{end}';labels=after
c+='\n'.join('#print axioms '+n for n in names)+'\nend CurrentMain.Current535NonzeroBandCheck\n';assert len(names)==38;assert not(HERE/'Current535NonzeroBandCheck.lean').exists();(HERE/'Current535NonzeroBandCheck.lean').write_text(c)
records=[]
for ordinal in range(253,277):
 r=recipes['children'][ordinal];old,new,rank=r['old'],r['new'],r['rank'];assert 6<=old<=13 and 14<=new<=25 and rank==1 and len(word['frames'][old])==1 and len(word['frames'][new])==2
 records.append({'ordinal':ordinal,'key':[old,new,rank],'ordered_old_descriptor':word['frames'][old],'ordered_new_descriptor':word['frames'][new],'normalized_record_sha256':hashlib.sha256(json.dumps(r,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
# Read-only label trace sanity check, not a scalar/operator execution or Lean replay.
label_audit={}
for orientation in ('forward','backward'):
 labels=list(word['start'])+[0]*8;assert len(labels)==736;checkpoints={}
 for i in range(10691,10951):
  r=m.decode_row(i,programs[orientation][i],keymap);e=r['event']
  if e[0]=='relabel':
   assert labels[e[1]]==e[2],(orientation,i,labels[e[1]],e)
   labels[e[1]]=e[3]
  else:
   assert e[0]=='add' and labels[e[1]]==labels[e[2]]==r['scalarFrame']
  if i in (10902,10926,10950):checkpoints[str(i)]={'labels':list(labels),'sha256':hashlib.sha256(json.dumps(labels,separators=(',',':')).encode()).hexdigest()}
 label_audit[orientation]=checkpoints
audit=save('LITERAL_PROJECTION.json',{'status':'SOURCE_LITERAL_ONLY','current_snapshot':'7dfa22b109996e48db68daac3706e7a49a43002b','inputs':[pp,rp,wp],'decoder':pin(P/'decode_current45.py'),'generator':pin(__file__),'blocks':blocks,'raw_rows':rawrows,'typed_rows':rows,'histograms':hist,'catalog_records':records,'stop_boundary':{'raw_index':10951,'forward':programs['forward'][10951],'backward':programs['backward'][10951]},'read_only_label_trace':label_audit,'label_trace_qualification':'Source-mapping sanity check only, seeded by canonical starts and accepted212 projected rows; no Lean prefix replay or scalar/operator execution.','no_scalar_or_operator_execution':True})
scanner=P.parent/'f19-label-recipe-coverage-proposal/tools/lean_delimiter_advisory.py';ad=[]
for f in HERE.glob('*.lean'):
 t=time.monotonic();r=subprocess.run(['python3',str(scanner),str(f)],capture_output=True,text=True,check=True);ad.append({'source':pin(f),'result':json.loads(r.stdout),'elapsed_seconds':time.monotonic()-t})
adv=save('DELIMITER_ADVISORY.json',{'helper':pin(scanner),'results':ad,'advisory_only':True})
Q=Path('/workspace/scratch/c569c316cd54/recovery_20261011/post114_reconstruction')
scope=save('SOURCE_SCOPE.json',{'status':'FROZEN_7DFA_SOURCE_ONLY_NEW_MAIN_RECONCILIATION_DISPATCH_HOLD','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'authority':'Root direct approval2026-10-12T15:49:04UTC for12/10/2 source preparation and reviewed first check. Integration15:50:56 imposed a dispatch hold pending exact new-main9594 reconciliation; this packet remains explicitly7dfa-bound.','next_owner':'/root/prove_main_bank_routing','sources':[pin(HERE/n)for n in ['Current535NonzeroBandData.lean','Current535NonzeroBandCheck.lean']],'literal_projection':audit,'advisory':adv,'prior212_acceptance':pin(Q/'bank/current535_entrance_band/ACCEPTANCE.json'),'prior212_terminal':pin(Q/'machine/CURRENT535_COVERAGE212_TERMINAL_INDEPENDENT_REVIEW.json'),'blocks':blocks,'local_scope':{'total':12,'retained':10,'fresh':2},'external_pairs':2213,'new_rows_each':48,'new_histogram_each':{'ADD':24,'relabel':24},'composed_rows_each':260,'composed_histogram_each':{'ADD':164,'relabel':96},'full_label_domain':736,'frame_count':997,'child_count':2927,'new_probe_count':38,'resources':{'hard_seconds_each':60,'hard_AS_bytes':4294967296,'review_seconds_each':45,'review_VM_bytes':3758096384,'fresh_jobs_max':2,'async':False,'maxRecDepth':8192,'maxHeartbeats':2000000,'shared_serial_slot':1,'stop':'First failure/review, no automatic retry or cap increase.'},'baseline':{'current90_row_Check_seconds':22.862992650989327,'current90_row_Check_VM':2303229952,'qualification':'Different input sizes and24 nonzero-old-frame keys; new cost/fit unmeasured, no throughput inference.'},'success':'Two below-review passes;38 clean probes; full236/260 checkpoints and260-row composed label/catalog predicates.','limits':['No assumption of accepted operator equations for all24 new keys.','Only canonical labels, signed annotation/nonzero denominator and exact directed child/rank checks.','Raw10951 higher-frame joins, omitted pre-A/adapter semantics and full physical-work/scalar endpoint remain open.'],'proof_reuse':'Existing arbitrary-value sparse_checkpoint handles12 then12 label updates; complement724/724 unchanged. Accepted212 append/checkpoints consumed directly, with zero prefix predicate replay. Default0 of values functions is outside support and never overwrites those labels.','compiler_status':'Unstarted; main9594 reconciliation hold must be resolved in addition to independent source/API and binding seals.'})
print(json.dumps(scope));print(json.dumps([pin(HERE/n)for n in ['Current535NonzeroBandData.lean','Current535NonzeroBandCheck.lean']]))
