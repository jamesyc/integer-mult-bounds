from pathlib import Path
HERE=Path(__file__).resolve().parent
s='''/- Fresh current535 canonical-frame checks for exactly raw10691..10735, both orientations.
The current997-frame catalog and initializer are certified at this literal boundary.
No pre-A admissibility, omitted-adapter, scalar endpoint or operator conclusion. -/
import Current535CoverageData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current535CoverageCheck
open CurrentMain.CanonicalFrameCoverage
namespace Data := CurrentMain.Current535CoverageData

'''
# Lean namespace aliases use the established syntax below.
s=s.replace('namespace Data := CurrentMain.Current535CoverageData','namespace Data = CurrentMain.Current535CoverageData')
# Avoid any namespace alias extension: use fully qualified short namespace via open parent.
s=s.replace('namespace Data = CurrentMain.Current535CoverageData','')
names=[]
def th(name,text):
 global s
 names.append(name);s+='theorem '+name+' '+text+'\n\n'
th('current_table_shape', ':\n    Data.frameDimensions.size = 997 ∧ Data.initialOriginalLabels.size = 728 ∧\n    Data.children.size = 2927 := by decide +kernel')
for letter,begin,size in [('A',10691,24),('B',10715,21)]:
 th('exact_'+letter+'_source_indices',f':\n    Data.forward{letter}.map Row.sourceIndex = List.range\' {begin} {size} ∧\n    Data.backward{letter}.map Row.sourceIndex = List.range\' {begin} {size} := by decide +kernel')
for o in ['forward','backward']:
 for letter,prior,end in [('A',0,24),('B',24,45)]:
  row=f'Data.{o}{letter}';labels=f'Data.labels{prior}';stem=f'{o}_{letter}'
  th(stem+'_labels_checked',f':\n    labelRowsB {row} {labels} = true := by decide +kernel')
  th(stem+'_children_checked',f':\n    childRowsB Data.data {row} = true := by decide +kernel')
  th(stem+'_checked',f':\n    checkRows Data.data {row} {labels} = true := by\n  rw [checkRows_factor]\n  exact Bool.and_eq_true_iff.mpr ⟨{stem}_labels_checked, {stem}_children_checked⟩')
  th(stem+'_wellLabelled',f':\n    LemmaG.Stream.WellLabelled ({row}.map Row.event) {labels} :=\n  checkRows_wellLabelled Data.data {row} {labels} {stem}_checked')
  th(f'{o}_support{end}',f':\n    ({row}.map Row.event).all (supportedB Data.support{end}) = true := by decide +kernel')
  th(f'{o}_touched{end}',f':\n    Data.support{end}.all (fun r =>\n      LemmaG.Stream.labRun ({row}.map Row.event) {labels} r ==\n        (2 : FrameLabel 997)) = true := by decide +kernel')
  th(f'{o}_checkpoint{end}',f':\n    LemmaG.Stream.labRun ({row}.map Row.event) {labels} = Data.labels{end} :=\n  sparse_checkpoint {row} {labels} (fun _ => (2 : FrameLabel 997))\n    Data.support{end} {o}_support{end} {o}_touched{end}')
 th(f'{o}_composed_wellLabelled45',f':\n    LemmaG.Stream.WellLabelled ((Data.{o}A ++ Data.{o}B).map Row.event) Data.labels0 := by\n  rw [List.map_append]\n  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr\n  refine ⟨{o}_A_wellLabelled, ?_⟩\n  rw [{o}_checkpoint24]\n  exact {o}_B_wellLabelled')
 th(f'{o}_composed_checkpoint45',f':\n    LemmaG.Stream.labRun ((Data.{o}A ++ Data.{o}B).map Row.event) Data.labels0 = Data.labels45 := by\n  rw [List.map_append, LemmaG.Stream.labRun_append, {o}_checkpoint24]\n  exact {o}_checkpoint45')
s+='\n'.join('#print axioms '+n for n in names)+'\nend CurrentMain.Current535CoverageCheck\n'
s=s.replace('Data.','Current535CoverageData.')
(HERE/'Current535CoverageCheck.lean').write_text(s)
print(len(names),'probes')
