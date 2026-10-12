from pathlib import Path
import collections,datetime,hashlib,importlib.util,json,re,subprocess,time
HERE=Path(__file__).resolve().parent;P=HERE.parent
spec=importlib.util.spec_from_file_location('owned_current_decoder',P/'decode_current45.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):p=Path(p);return dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
def save(n,x):p=HERE/n;assert not p.exists();p.write_text(json.dumps(x,indent=2)+'\n');return pin(p)
programs,program_pin=m.load(m.LOCAL/'LOCAL-PROGRAMS.json.gz','d403a1b263a43a40448046c7661919206d222bf37e85b63a4a8950144b8c158f')
recipes,recipe_pin=m.load(m.LOCAL/'CLIFFORD-RECIPES.json','577a1be13f5140d9c3997637784b2f812f46b24c61877699430b02de4f662102')
keymap={(x['old'],x['new']):(i,x['rank'])for i,x in enumerate(recipes['children'])};assert len(keymap)==2927 and keymap[0,3]==(1,1)
rows={};supports={};hist={}
for o in ('forward','backward'):
 rows[o]=[m.decode_row(i,programs[o][i],keymap)for i in range(10736,10784)]
 supports[o]=[[r['event'][1]for r in block if r['event'][0]=='relabel']for block in (rows[o][:24],rows[o][24:])]
 hist[o]=[dict(collections.Counter(r['event'][0]for r in block))for block in (rows[o][:24],rows[o][24:])]
 assert all(r['childRef'] is None or r['childRef']==[1,1]for r in rows[o])
expected=[[488,489,498,486,487,500,536,537,546,534,535,548],[586,588,464,465]]
assert supports=={o:expected for o in rows}
s='''/- Exact current535 source rows10736..10783 in both orientations.
Fresh source literals; the historical child6 final register pair is different.
No operator, full-stream or omitted-adapter conclusion. -/
import Current535CoverageCheck

set_option Elab.async false
namespace CurrentMain.Current535Child003Data
open CurrentMain.CanonicalFrameCoverage
'''
for o in rows:
 for letter,block in [('C',rows[o][:24]),('D',rows[o][24:])]:
  s+=f'def {o}{letter} : List (Row 997) := [\n'+',\n'.join(m.lean_row(r)for r in block)+'\n]\n\n'
for num,support,prev in [(69,expected[0],'Current535CoverageData.labels45'),(93,expected[1],'labels69')]:
 s+=f'def support{num} : List Register := ['+', '.join(map(str,support))+']\n'
 s+=f'def labels{num} (r : Register) : FrameLabel 997 :=\n  if r ∈ support{num} then 3 else {prev} r\n'
s+='end CurrentMain.Current535Child003Data\n';(HERE/'Current535Child003Data.lean').write_text(s)
c='''/- Exact48-row current535 extension, reusing the accepted45-row predicate and checkpoint.
Only canonical label and directed catalog coverage; physical/operator suppliers remain open. -/
import Current535Child003Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current535Child003Check
open CurrentMain.CanonicalFrameCoverage

''';names=[]
def th(name,text):
 global c
 names.append(name);c+='theorem '+name+' '+text+'\n\n'
for letter,start in [('C',10736),('D',10760)]:
 th(f'exact_{letter}_source_indices',f':\n    Current535Child003Data.forward{letter}.map Row.sourceIndex = List.range\' {start} 24 ∧\n    Current535Child003Data.backward{letter}.map Row.sourceIndex = List.range\' {start} 24 := by decide +kernel')
for o in ('forward','backward'):
 prefix=f'(Current535CoverageData.{o}A ++ Current535CoverageData.{o}B)'
 previousWL=f'Current535CoverageCheck.{o}_composed_wellLabelled45';previousCP=f'Current535CoverageCheck.{o}_composed_checkpoint45'
 for letter,start,end in [('C',45,69),('D',69,93)]:
  r=f'Current535Child003Data.{o}{letter}';labels='Current535CoverageData.labels45'if start==45 else'Current535Child003Data.labels69';stem=f'{o}_{letter}';support=f'Current535Child003Data.support{end}';after=f'Current535Child003Data.labels{end}'
  th(stem+'_labels_checked',f':\n    labelRowsB {r} {labels} = true := by decide +kernel')
  th(stem+'_children_checked',f':\n    childRowsB Current535CoverageData.data {r} = true := by decide +kernel')
  th(stem+'_checked',f':\n    checkRows Current535CoverageData.data {r} {labels} = true := by\n  rw [checkRows_factor]\n  exact Bool.and_eq_true_iff.mpr ⟨{stem}_labels_checked, {stem}_children_checked⟩')
  th(stem+'_wellLabelled',f':\n    LemmaG.Stream.WellLabelled ({r}.map Row.event) {labels} :=\n  checkRows_wellLabelled Current535CoverageData.data {r} {labels} {stem}_checked')
  th(f'{o}_support{end}',f':\n    ({r}.map Row.event).all (supportedB {support}) = true := by decide +kernel')
  th(f'{o}_touched{end}',f':\n    {support}.all (fun r =>\n      LemmaG.Stream.labRun ({r}.map Row.event) {labels} r ==\n        (3 : FrameLabel 997)) = true := by decide +kernel')
  th(f'{o}_checkpoint{end}',f':\n    LemmaG.Stream.labRun ({r}.map Row.event) {labels} = {after} :=\n  sparse_checkpoint {r} {labels} (fun _ => (3 : FrameLabel 997))\n    {support} {o}_support{end} {o}_touched{end}')
  prefix=f'({prefix} ++ {r})'
  th(f'{o}_composed_wellLabelled{end}',f':\n    LemmaG.Stream.WellLabelled ({prefix}.map Row.event) Current535CoverageData.labels0 := by\n  rw [List.map_append]\n  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr\n  refine ⟨{previousWL}, ?_⟩\n  rw [{previousCP}]\n  exact {stem}_wellLabelled')
  th(f'{o}_composed_checkpoint{end}',f':\n    LemmaG.Stream.labRun ({prefix}.map Row.event) Current535CoverageData.labels0 = {after} := by\n  rw [List.map_append, LemmaG.Stream.labRun_append, {previousCP}]\n  exact {o}_checkpoint{end}')
  previousWL=f'{o}_composed_wellLabelled{end}';previousCP=f'{o}_composed_checkpoint{end}'
c+='\n'.join('#print axioms '+n for n in names)+'\nend CurrentMain.Current535Child003Check\n';(HERE/'Current535Child003Check.lean').write_text(c)
audit=save('LITERAL_PROJECTION.json',{'status':'SOURCE_LITERAL_ONLY','source_commit':'7dfa22b109996e48db68daac3706e7a49a43002b','inputs':[program_pin,recipe_pin],'decoder':pin(P/'decode_current45.py'),'generator':pin(__file__),'raw_range':[10736,10783],'raw_rows':{o:programs[o][10736:10784]for o in rows},'typed_rows':rows,'supports':supports,'histograms':hist,'current_child':recipes['children'][1],'old_source_difference':'Final support pair464/465 differs from oldchild6 pair656/657; no old finite predicate is transported.'})
scanner=P.parent/'f19-label-recipe-coverage-proposal/tools/lean_delimiter_advisory.py';ad=[]
for file in HERE.glob('*.lean'):
 t=time.monotonic();r=subprocess.run(['python3',str(scanner),str(file)],capture_output=True,text=True,check=True);ad.append({'source':pin(file),'result':json.loads(r.stdout),'elapsed_seconds':time.monotonic()-t})
adv=save('DELIMITER_ADVISORY.json',{'helper':pin(scanner),'results':ad,'advisory_only':True})
scope=save('SOURCE_SCOPE.json',{'status':'SOURCE_FROZEN_CURRENT535_CHILD003_EQUIVALENT_EXTENSION','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sources':[pin(HERE/n)for n in ['Current535Child003Data.lean','Current535Child003Check.lean']],'literal_inverse':audit,'advisory':adv,'prior_owner_acceptance':pin(Path('/workspace/scratch/c569c316cd54/recovery_20261011/post114_reconstruction/bank/current535_coverage45/ACCEPTANCE.json')),'source_scope':{'raw_inclusive':[10736,10783],'new_rows_each':48,'split':[24,24],'new_histogram_each':{'ADD':32,'relabel':16},'new_child_ordinal':1,'new_child_key':[0,3,1],'ordered_descriptor':[486],'checkpoints':[45,69,93],'supports':expected,'full_label_domain':736,'frame_count':997,'child_count':2927,'composed_rows_each':93,'composed_histogram_each':{'ADD':63,'relabel':30}},'local_scope':{'total':6,'retained':4,'fresh':2},'external_pairs':2213,'new_probe_count':len(names),'proof_reuse':'Same parameterized factorization and multivalue sparse helper; append consumes accepted45 directly. Fresh signed coefficients, indices and changed register operands are not transported from f19.','resources':{'hard_seconds_each':60,'hard_AS_bytes':4294967296,'review_seconds_each':45,'review_VM_bytes':3758096384,'async':False,'shared_serial_slot':1,'fresh_jobs_max':2,'baseline':'Current45 Check17.659996682s/2302177280VM; no next-fit or throughput inference.'},'completion':'Two below-review passes,38 clean probes, full69/93 checkpoint and93-row compositions; first failure/review stops.','limits':['Current0→3/[486] operator and complete Event/physical execution remain separate suppliers.','Pre-A projection/adapters and full stream are outside.','Historical743 result remains unchanged; only generic proof structure is reused.'],'compiler_admission':'Requires accepted45 terminal seal plus independent science/API and integration binding/current guard.'})
print(json.dumps(scope));print(json.dumps([pin(HERE/n)for n in ['Current535Child003Data.lean','Current535Child003Check.lean']]))
