from pathlib import Path
import collections,datetime,hashlib,importlib.util,json,re,subprocess,time
HERE=Path(__file__).resolve().parent;B=HERE.parent.parent;Q=Path('/workspace/scratch/c569c316cd54/recovery_20261011/post114_reconstruction');P=HERE.parent/'current799-first33';PREV=HERE.parent/'current799-next32';starttime=time.monotonic()
spec=importlib.util.spec_from_file_location('owned_current_decoder',P/'decode_current33.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):p=Path(p);return dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
def save(n,x):p=HERE/n;assert not p.exists();p.write_text(json.dumps(x,indent=2)+'\n');return pin(p)
programs,pp=m.load(m.LOCAL/'LOCAL-PROGRAMS.json.gz','ce194f8465079db575a9ce17ccee1396fa4de0210e2817da2525f95f4f93ebde')
recipes,rp=m.load(m.LOCAL/'CLIFFORD-RECIPES.json','20dddfce0ded7e41dc507939df7297bd98aec1286e05d7dbf18000d57e69a0b7')
can,cp=m.load(m.LOCAL/'CANONICAL-WORD.json.gz','f1c2ede9276d4447c5857d0e9d32adb52f987b8adb643b45bde2c172d88c6ee9')
keys=[[x['old'],x['new'],x['rank']]for x in recipes['children'][:353]];km={(a,b):(i,k)for i,(a,b,k)in enumerate(keys)};assert len(km)==353
old=json.loads((PREV/'LITERAL_PROJECTION.json').read_text());assert old['catalog_prefix_keys']==keys[:15]
segments=[('H',9370,9394,153),('I',9394,9418,177)];rows={o:{letter:[m.decode_row(i,programs[o][i],km)for i in range(a,z)]for letter,a,z,_ in segments}for o in ['forward','backward']};supports={};updates={}
for letter,a,z,end in segments:
 rs=rows['forward'][letter];assert collections.Counter(r['event'][0]for r in rs)==({'add':16,'scale':4,'relabel':4}if letter=='H'else {'add':12,'relabel':12});updates[end]=[(r['event'][1],r['event'][3])for r in rs if r['event'][0]=='relabel'];supports[end]=[i for i,l in updates[end]];assert len(set(supports[end]))==(4 if letter=='H'else 12)
 for o in rows:
  assert collections.Counter(r['event'][0]for r in rows[o][letter])==({'add':16,'scale':4,'relabel':4}if letter=='H'else {'add':12,'relabel':12})
  assert [(r['event'][1],r['event'][3])for r in rows[o][letter]if r['event'][0]=='relabel']==updates[end]
labels=old['full_checkpoint_readback']['129'].copy();assert len(labels)==736
initial=labels.copy();checkpoints={}
for letter,a,z,end in segments:
 expected=labels.copy()
 for i,l in updates[end]:expected[i]=l
 for o in rows:
  state=labels.copy()
  for r in rows[o][letter]:
   e=r['event']
   if e[0]=='relabel':assert state[e[1]]==e[2];state[e[1]]=e[3]
   elif e[0]=='add':assert state[e[1]]==state[e[2]]==r['scalarFrame']and e[3][1]!=0
   else:assert e[0]=='scale'and state[e[1]]==r['scalarFrame']and e[2][1]!=0
  assert state==expected
 labels=expected;checkpoints[end]=labels.copy()
assert all(programs[o][9418][0]=='climb'for o in rows)
used=sorted({r['childRef'][0]for o in rows for part in rows[o].values()for r in part if r['childRef']});assert max(used)==352 and min(used)==330
assert all(r['event'][2]>0 for o in rows for part in rows[o].values()for r in part if r['childRef'])
s='''/- Exact current PR799 nonzero-old48 rows, zero-based raw9370..9417, both orientations.
Only label/catalog coverage; sixteen nonzero-old operator suppliers and actual entrance remain separate.
Author-checked conditional source context: kappa=1661634653669567/1000000000000000000.
Attribution: selected PR799 source and accepted PR509/checker interfaces. -/
import Current799Next32Check

set_option Elab.async false
namespace CurrentMain.Current799Nonzero48Data
open CurrentMain.CanonicalFrameCoverage
'''
s+=m.emit_array('children','(ChildKey 1005)',['⟨'+', '.join(map(str,k))+'⟩'for k in keys])
for o in rows:
 for letter,_,_,_ in segments:s+=f'def {o}{letter} : List (Row 1005) := [\n'+',\n'.join(m.lean_row(r)for r in rows[o][letter])+'\n]\n\n'
s+='''def data : SelectedData 1005 :=
  ⟨Current799First33CoverageData.frameDimensions,
    Current799First33CoverageData.initialOriginalLabels, children, forwardH ++ forwardI, backwardH ++ backwardI⟩
'''
for letter,a,z,end in segments:
 s+=f'def support{end} : List Register := {supports[end]}\n'
 groups={l:[i for i,v in updates[end]if v==l]for l in sorted(set(l for i,l in updates[end]))};values=list(groups)
 s+=f'def target{end} (r : Register) : FrameLabel 1005 :=\n  '
 for v in values[:-1]:s+=f'if r ∈ ({groups[v]} : List Register) then {v} else '
 s+=str(values[-1])+'\n';before='Current799Next32Data.labels129'if end==153 else 'labels153';s+=f'def labels{end} (r : Register) : FrameLabel 1005 :=\n  if r ∈ support{end} then target{end} r else {before} r\n'
s+='end CurrentMain.Current799Nonzero48Data\n';f=HERE/'Current799Nonzero48Data.lean';assert not f.exists();f.write_text(s)
c='''/- Two exact24-row nonzero-old chunks extend the accepted129-row selected current799 prefix.
Multivalue sparse checkpoints retain every736 label coordinate.
No operator realization or actual entrance execution is claimed. -/
import Current799Nonzero48Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current799Nonzero48Check
open CurrentMain.CanonicalFrameCoverage

''';names=[]
def th(name,text):
 global c
 names.append(name);c+='theorem '+name+' '+text+'\n\n'
th('catalog_prefix_shape',': Current799Nonzero48Data.children.size = 353 := by decide +kernel')
indexgoals=[f"Current799Nonzero48Data.{o}{letter}.map Row.sourceIndex = List.range' {a} {z-a}"for o in rows for letter,a,z,end in segments];th('exact_source_indices',':\n    '+' ∧\n    '.join(indexgoals)+' := by decide +kernel')
for o in rows:
 prefix=f'((((((Current799First33CoverageData.{o}A ++ Current799First33CoverageData.{o}B) ++ Current799Next16Data.{o}C) ++ Current799Next48Data.{o}D) ++ Current799Next48Data.{o}E) ++ Current799Next32Data.{o}F) ++ Current799Next32Data.{o}G)';before='Current799Next32Data.labels129';prevWL=f'Current799Next32Check.{o}_composed_wellLabelled129';prevCP=f'Current799Next32Check.{o}_composed_checkpoint129'
 for letter,a,z,end in segments:
  r=f'Current799Nonzero48Data.{o}{letter}';data='Current799Nonzero48Data.data';support=f'Current799Nonzero48Data.support{end}';target=f'Current799Nonzero48Data.target{end}';after=f'Current799Nonzero48Data.labels{end}';stem=o+'_'+letter
  th(stem+'_labels_checked',f': labelRowsB {r} {before} = true := by decide +kernel')
  th(stem+'_children_checked',f': childRowsB {data} {r} = true := by decide +kernel')
  th(stem+'_checked',f': checkRows {data} {r} {before} = true := by\n  rw [checkRows_factor]\n  exact Bool.and_eq_true_iff.mpr ⟨{stem}_labels_checked, {stem}_children_checked⟩')
  th(stem+'_wellLabelled',f':\n    LemmaG.Stream.WellLabelled ({r}.map Row.event) {before} :=\n  checkRows_wellLabelled {data} {r} {before} {stem}_checked')
  th(o+f'_support{end}',f':\n    ({r}.map Row.event).all (supportedB {support}) = true := by decide +kernel')
  th(o+f'_touched{end}',f':\n    {support}.all (fun r =>\n      LemmaG.Stream.labRun ({r}.map Row.event) {before} r == {target} r) = true := by decide +kernel')
  th(o+f'_checkpoint{end}',f':\n    LemmaG.Stream.labRun ({r}.map Row.event) {before} = {after} :=\n  sparse_checkpoint {r} {before} {target}\n    {support} {o}_support{end} {o}_touched{end}')
  prefix=f'({prefix} ++ {r})'
  th(o+f'_composed_wellLabelled{end}',f':\n    LemmaG.Stream.WellLabelled ({prefix}.map Row.event) Current799First33CoverageData.labels0 := by\n  rw [List.map_append]\n  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr\n  refine ⟨{prevWL}, ?_⟩\n  rw [{prevCP}]\n  exact {stem}_wellLabelled')
  th(o+f'_composed_checkpoint{end}',f':\n    LemmaG.Stream.labRun ({prefix}.map Row.event) Current799First33CoverageData.labels0 = {after} := by\n  rw [List.map_append, LemmaG.Stream.labRun_append, {prevCP}]\n  exact {o}_checkpoint{end}')
  before=after;prevWL=o+f'_composed_wellLabelled{end}';prevCP=o+f'_composed_checkpoint{end}'
c+='\n'.join('#print axioms '+n for n in names)+'\nend CurrentMain.Current799Nonzero48Check\n';f=HERE/'Current799Nonzero48Check.lean';assert not f.exists();f.write_text(c);assert len(names)==38 and c.count('decide +kernel')==18
projection=save('LITERAL_PROJECTION.json',{'status':'READ_ONLY_STRICT_SOURCE_PROJECTION','head':'f567884aeb8851b6e794af1184119a3bfbe1e631','inputs':[pp,rp,cp],'decoder':pin(P/'decode_current33.py'),'preparer':pin(__file__),'range_zero_based_inclusive':[9370,9417],'segments':segments,'raw_rows':{o:programs[o][9370:9418]for o in rows},'typed_rows':rows,'catalog_prefix_keys':keys,'catalog_records':[recipes['children'][i]for i in used],'ordered_descriptors':{str(i):can['frames'][i]for i in range(9,25)},'supports':supports,'updates':updates,'full_checkpoint_readback':checkpoints,'prior_checkpoint_source':pin(PREV/'LITERAL_PROJECTION.json'),'unchanged_complements':[732,724],'elapsed_seconds':time.monotonic()-starttime})
scanner=HERE.parent/'f19-label-recipe-coverage-proposal/tools/lean_delimiter_advisory.py';ad=[]
for f in HERE.glob('*.lean'):
 st=time.monotonic();r=subprocess.run(['/usr/bin/python3.13','-I','-B',str(scanner),str(f)],capture_output=True,text=True,check=True);ad.append({'source':pin(f),'result':json.loads(r.stdout),'elapsed_seconds':time.monotonic()-st})
adv=save('DELIMITER_ADVISORY.json',{'helper':pin(scanner),'advisory_only':True,'results':ad})
terminal=Path('/workspace/shared/integer-mult-git/worktrees/signed/research/reviews/bank-current799-next32/CHECK_TERMINAL_INDEPENDENT_REVIEW.json')
probes={'Current799Nonzero48Check':['CurrentMain.Current799Nonzero48Check.'+x for x in names],'Current799Nonzero48Data':[]}
scope=save('SOURCE_SCOPE.json',{'status':'SOURCE_ONLY_CURRENT799_NONZERO48_PENDING_SCIENCE_BINDING_ADMISSION','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sources':[pin(HERE/n)for n in ['Current799Nonzero48Data.lean','Current799Nonzero48Check.lean']],'literal_projection':projection,'delimiter_advisory':adv,'selected_artifact_verification':pin(Q.parent/'new_main_f567884_artifacts/VERIFIED_ARTIFACTS.json'),'prior_acceptance':pin(Q/'bank/current799_next32_check/ACCEPTANCE.json'),'prior_independent_terminal':pin(terminal) if terminal.exists() else {'status':'PENDING_INDEPENDENT129_TERMINAL','owner_acceptance':pin(Q/'bank/current799_next32_check/ACCEPTANCE.json')},'prior_source_pins':[pin(PREV/n)for n in ['Current799Next32Data.lean','Current799Next32Check.lean']],'source_scope':{'raw_zero_based_inclusive':[9370,9417],'new_rows_each':48,'chunk_lengths':[24,24],'histogram_each':{'ADD':28,'SCALE':4,'relabel':16},'child_ordinals':used,'directed_key_ranks':[keys[i]for i in used],'directed_descriptors':[{'old':can['frames'][keys[i][0]],'new':can['frames'][keys[i][1]]}for i in used],'catalog_prefix_count':353,'full_catalog_count':2949,'frame_count':1005,'label_registers':736,'checkpoints':[129,153,177],'supports':supports,'updates':updates,'unchanged_complements':[732,724],'composed_histogram_each':{'ADD':101,'SCALE':4,'relabel':72},'next_excluded_raw':9418,'next_excluded_key':programs['forward'][9418][3:5]},'local_scope':{'modules':12,'current':10,'pending':2},'external_pairs':2213,'expected_probes':probes,'finite_decisions':18,'proof_reuse':'Accepted factorization, checkRows soundness, multivalue sparse_checkpoint and append laws. No prefix replay, new generic induction or table-wide decisions.','resource_proposal':{'hard_seconds_each':60,'hard_vm_bytes':4294967296,'review_seconds_each':45,'review_vm_bytes':3758096384,'shared_slots':2,'owner_serial_jobs':1,'new_jobs_max':2,'Elab.async':False,'baseline':'Prior32 Data4.641843326s/2096410624VM; Check7.059551671s/2163838976VM. Nonzero-old/SCALE48 fit unmeasured; no throughput extrapolation.'},'completion':'Both roots below review caps,38 complete standard-only probes and all current/import/output guards exact; stop at first failure or review.','authority':'Root2026-10-13 09:54:54 authorizes exact2dd73be7 source preparation, prospective12/10/2,38probes/18decisions,129-to153-to177. Require independent nonzero-old direction/denominator/353-key source/API and standard binding before any compiler.','excluded_scope':['Actual entrance/pre-A executor, all731 omitted phase/adapter rows and full-stream coverage.','Current nonzero-old records330..352 operator or physical realization.','Full2949 catalog and events from raw9418 onward.'],'compiler_runs':0})
print(json.dumps(scope));print('probes',len(names),'decisions',c.count('decide +kernel'))
