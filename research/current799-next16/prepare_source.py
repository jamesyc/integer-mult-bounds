from pathlib import Path
import collections,datetime,hashlib,importlib.util,json,re,subprocess,time
HERE=Path(__file__).resolve().parent;B=HERE.parent.parent;Q=Path('/workspace/scratch/c569c316cd54/recovery_20261011/post114_reconstruction');P=HERE.parent/'current799-first33';starttime=time.monotonic()
spec=importlib.util.spec_from_file_location('owned_current_decoder',P/'decode_current33.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):p=Path(p);return dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
def save(n,x):p=HERE/n;assert not p.exists();p.write_text(json.dumps(x,indent=2)+'\n');return pin(p)
programs,pp=m.load(m.LOCAL/'LOCAL-PROGRAMS.json.gz','ce194f8465079db575a9ce17ccee1396fa4de0210e2817da2525f95f4f93ebde')
recipes,rp=m.load(m.LOCAL/'CLIFFORD-RECIPES.json','20dddfce0ded7e41dc507939df7297bd98aec1286e05d7dbf18000d57e69a0b7')
can,cp=m.load(m.LOCAL/'CANONICAL-WORD.json.gz','f1c2ede9276d4447c5857d0e9d32adb52f987b8adb643b45bde2c172d88c6ee9')
keys=[[x['old'],x['new'],x['rank']] for x in recipes['children'][:4]];km={(a,b):(i,k) for i,(a,b,k) in enumerate(keys)};assert len(km)==4 and km[0,5]==(3,1)
old=json.loads((P/'LITERAL_PROJECTION.json').read_text());assert old['children']==keys[:3] and old['dimensions']==list(map(len,can['frames'])) and old['starts']==can['start']
rows={o:[m.decode_row(i,programs[o][i],km) for i in range(9274,9290)]for o in ['forward','backward']}
support=[474,475,480,481,490,491,526,527]
for o,rs in rows.items():
 assert collections.Counter(r['event'][0]for r in rs)=={'add':8,'relabel':8}
 assert [r['event'][1]for r in rs if r['event'][0]=='relabel']==support
 assert all(r['childRef'] in [None,[3,1]]for r in rs)
 assert programs[o][9290][3:5]==[0,6]
# Read-only source-level label/annotation inverse check from the retained checkpoint representation.
labels=list(can['start'])+[0]*8
for i in [558,572,559,582,560,570,561,584]:labels[i]=4
for o,rs in rows.items():
 state=labels.copy()
 for r in rs:
  e=r['event']
  if e[0]=='relabel':assert state[e[1]]==e[2];state[e[1]]=e[3]
  else:assert e[0]=='add' and state[e[1]]==state[e[2]]==r['scalarFrame'];assert e[3][1]!=0
 assert all(state[i]==(5 if i in support else labels[i])for i in range(736))
s='''/- Exact current PR799 next16 rows, zero-based raw9274..9289, both orientations.
Only canonical labels/catalog coverage; current record3 operator and actual entrance execution remain separate.
Author-checked conditional source context: kappa=1661634653669567/1000000000000000000.
Attribution: selected PR799 source and accepted PR509/checker interfaces. -/
import Current799First33CoverageCheck

set_option Elab.async false
namespace CurrentMain.Current799Next16Data
open CurrentMain.CanonicalFrameCoverage
'''
s+=m.emit_array('children','(ChildKey 1005)',['⟨'+', '.join(map(str,k))+'⟩' for k in keys])
for o,rs in rows.items():s+=f'def {o}C : List (Row 1005) := [\n'+',\n'.join(m.lean_row(r)for r in rs)+'\n]\n\n'
s+='''def data : SelectedData 1005 :=
  ⟨Current799First33CoverageData.frameDimensions,
    Current799First33CoverageData.initialOriginalLabels, children, forwardC, backwardC⟩
def support49 : List Register := [474, 475, 480, 481, 490, 491, 526, 527]
def labels49 (r : Register) : FrameLabel 1005 :=
  if r ∈ support49 then 5 else Current799First33CoverageData.labels33 r
end CurrentMain.Current799Next16Data
'''
f=HERE/'Current799Next16Data.lean';assert not f.exists();f.write_text(s)
c='''/- Fresh16-row directed0→5 extension of the accepted current799 first33.
The full sparse checkpoint and append use the accepted33 predicate without replay.
Only label/catalog/signed-denominator coverage; no operator or actual entrance execution. -/
import Current799Next16Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current799Next16Check
open CurrentMain.CanonicalFrameCoverage

''';names=[]
def th(name,text):
 global c
 names.append(name);c+='theorem '+name+' '+text+'\n\n'
th('catalog_prefix_shape',': Current799Next16Data.children.size = 4 := by decide +kernel')
th('exact_C_source_indices',":\n    Current799Next16Data.forwardC.map Row.sourceIndex = List.range' 9274 16 ∧\n    Current799Next16Data.backwardC.map Row.sourceIndex = List.range' 9274 16 := by decide +kernel")
for o in rows:
 r=f'Current799Next16Data.{o}C';lab='Current799First33CoverageData.labels33';data='Current799Next16Data.data';supportname='Current799Next16Data.support49';after='Current799Next16Data.labels49';stem=o+'_C'
 th(stem+'_labels_checked',f': labelRowsB {r} {lab} = true := by decide +kernel')
 th(stem+'_children_checked',f': childRowsB {data} {r} = true := by decide +kernel')
 th(stem+'_checked',f': checkRows {data} {r} {lab} = true := by\n  rw [checkRows_factor]\n  exact Bool.and_eq_true_iff.mpr ⟨{stem}_labels_checked, {stem}_children_checked⟩')
 th(stem+'_wellLabelled',f':\n    LemmaG.Stream.WellLabelled ({r}.map Row.event) {lab} :=\n  checkRows_wellLabelled {data} {r} {lab} {stem}_checked')
 th(o+'_support49',f':\n    ({r}.map Row.event).all (supportedB {supportname}) = true := by decide +kernel')
 th(o+'_touched49',f':\n    {supportname}.all (fun r =>\n      LemmaG.Stream.labRun ({r}.map Row.event) {lab} r ==\n        (5 : FrameLabel 1005)) = true := by decide +kernel')
 th(o+'_checkpoint49',f':\n    LemmaG.Stream.labRun ({r}.map Row.event) {lab} = {after} :=\n  sparse_checkpoint {r} {lab} (fun _ => (5 : FrameLabel 1005))\n    {supportname} {o}_support49 {o}_touched49')
 prefix=f'((Current799First33CoverageData.{o}A ++ Current799First33CoverageData.{o}B) ++ {r})';prevWL=f'Current799First33CoverageCheck.{o}_composed_wellLabelled33';prevCP=f'Current799First33CoverageCheck.{o}_composed_checkpoint33'
 th(o+'_composed_wellLabelled49',f':\n    LemmaG.Stream.WellLabelled ({prefix}.map Row.event) Current799First33CoverageData.labels0 := by\n  rw [List.map_append]\n  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr\n  refine ⟨{prevWL}, ?_⟩\n  rw [{prevCP}]\n  exact {stem}_wellLabelled')
 th(o+'_composed_checkpoint49',f':\n    LemmaG.Stream.labRun ({prefix}.map Row.event) Current799First33CoverageData.labels0 = {after} := by\n  rw [List.map_append, LemmaG.Stream.labRun_append, {prevCP}]\n  exact {o}_checkpoint49')
c+='\n'.join('#print axioms '+n for n in names)+'\nend CurrentMain.Current799Next16Check\n';f=HERE/'Current799Next16Check.lean';assert not f.exists();f.write_text(c);assert len(names)==20 and c.count('decide +kernel')==10
projection=save('LITERAL_PROJECTION.json',{'status':'READ_ONLY_STRICT_SOURCE_PROJECTION','head':'f567884aeb8851b6e794af1184119a3bfbe1e631','inputs':[pp,rp,cp],'decoder':pin(P/'decode_current33.py'),'preparer':pin(__file__),'range_zero_based_inclusive':[9274,9289],'raw_rows':{o:programs[o][9274:9290]for o in rows},'typed_rows':rows,'catalog_prefix_keys':keys,'catalog_record3':recipes['children'][3],'catalog_record3_normalized_sha256':hashlib.sha256(json.dumps(recipes['children'][3],sort_keys=True,separators=(',',':')).encode()).hexdigest(),'ordered_descriptors':[can['frames'][0],can['frames'][5]],'support':support,'prior_checkpoint_source':pin(P/'LITERAL_PROJECTION.json'),'labels49_readback_only':True,'unchanged_complement':728,'elapsed_seconds':time.monotonic()-starttime})
scanner=HERE.parent/'f19-label-recipe-coverage-proposal/tools/lean_delimiter_advisory.py';ad=[]
for f in HERE.glob('*.lean'):
 st=time.monotonic();r=subprocess.run(['/usr/bin/python3.13','-I','-B',str(scanner),str(f)],capture_output=True,text=True,check=True);ad.append({'source':pin(f),'result':json.loads(r.stdout),'elapsed_seconds':time.monotonic()-st})
adv=save('DELIMITER_ADVISORY.json',{'helper':pin(scanner),'advisory_only':True,'results':ad})
oldterminal=Q/'machine/CURRENT799_FIRST33_TERMINAL_INDEPENDENT_REVIEW.json';assert sha(oldterminal)=='bcee8dc869eefb2c877a4203da686a5fd7c69c9bf59cabb232613d0c66083084'
probes={ 'Current799Next16Check':['CurrentMain.Current799Next16Check.'+x for x in names],'Current799Next16Data':[]}
scope=save('SOURCE_SCOPE.json',{'status':'SOURCE_ONLY_CURRENT799_NEXT16','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sources':[pin(HERE/n)for n in ['Current799Next16Data.lean','Current799Next16Check.lean']],'literal_projection':projection,'delimiter_advisory':adv,'selected_artifact_verification':pin(Q.parent/'new_main_f567884_artifacts/VERIFIED_ARTIFACTS.json'),'prior_acceptance':pin(Q/'bank/current799_first33/ACCEPTANCE.json'),'prior_independent_terminal':pin(oldterminal),'prior_source_pins':[pin(P/n)for n in ['Current799First33CoverageData.lean','Current799First33CoverageCheck.lean']],'source_scope':{'raw_zero_based_inclusive':[9274,9289],'new_rows_each':16,'histogram_each':{'ADD':8,'relabel':8},'child_ordinal':3,'directed_key_rank':[0,5,1],'ordered_target_descriptor':[75],'signed_denominators':[1,2],'catalog_prefix_count':4,'full_catalog_count':2949,'frame_count':1005,'label_registers':736,'checkpoint_from_to':[33,49],'support':support,'unchanged_complement':728,'composed_histogram_each':{'ADD':33,'relabel':16},'next_excluded_raw':9290,'next_excluded_key':[0,6]},'local_scope':{'modules':6,'current':4,'pending':2},'external_pairs':2213,'expected_probes':probes,'finite_decisions':10,'proof_reuse':'Exact accepted factorization, checkRows soundness, sparse_checkpoint and append theorem architecture. Fresh16 literal rows each; frame dimensions/728 starts reuse accepted33 data. New catalog contains first4 original keys, no full-catalog theorem. Prior33 decisions are not repeated.','resource_proposal':{'hard_seconds_each':60,'hard_vm_bytes':4294967296,'review_seconds_each':45,'review_vm_bytes':3758096384,'shared_slots':2,'owner_serial_jobs':1,'new_jobs_max':2,'Elab.async':False,'baseline':'Accepted33 Data6.0585s/2097295360VM; Check9.3642s/2296922112VM. Next16 fit unmeasured; no throughput extrapolation.'},'completion':'Both roots below review caps,20 complete standard-only probes, all current/import/output guards exact; stop at first failure or review.','authority':'Root2026-10-13 07:54 prepares next current16 rows independently of frame operator redesign; integration to review concrete closure/probes/decisions before bounded admission.','excluded_scope':['Actual entrance/pre-A executor, all731 omitted phase/adapter rows and full-stream coverage.','Current record3/key0→5 operator/physical realization, separate frame task.','Full2949 catalog and subsequent key0→6.'],'compiler_runs':0})
print(json.dumps(scope));print('probes',len(names),'decisions',c.count('decide +kernel'))
