from pathlib import Path
import re
out=Path(__file__).resolve().parent;P=out.parent
prior=['PilotData.{d}','NextData.{d}','BatchData.{d}A','BatchData.{d}B','Child34Data.{d}C','Child34Data.{d}D','Child5Data.{d}E','Child5Data.{d}F','Child5TailData.{d}G','Child5TailData.{d}H','Child5BodyData.{d}I','Child5BodyData.{d}J','Child5MoreData.{d}K','Child5MoreData.{d}L']
chunks=[('M',11400,24,573),('N',11424,24,597),('O',11448,24,621),('P',11472,24,645),('Q',11496,24,669),('R',11520,26,695)]
def pref(d,i):
 ls=[x.format(d=d)for x in prior]+[f'StaticGapData.{d}{k}'for k,*_ in chunks[:i+1]]
 s=ls[0]
 for x in ls[1:]:s=f'({s} ++ {x})'
 return f'({s}.map Row.event)'
for j,part in enumerate(('A','B')):
 name='StaticGapCheck'+part
 s=f'''/- Selected static-label gap: small factored decisions with empty-support boundaries.
Child lookup is vacuous because every new row is ADD. Accepted 549-row proofs are reused.
No omitted-adapter, scalar or physical/operator interpretation is asserted. -/
import F19Coverage{'StaticGapData' if j==0 else 'StaticGapCheckA'}

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.{name}
open CurrentMain.F19SelectedCoverage

'''
 for i in range(j*3,j*3+3):
  k,raw,n,end=chunks[i];prevlabel='Child5MoreData.labels549'if i==0 else f'StaticGapData.labels{chunks[i-1][3]}'
  prevns='Child5MoreCheck.'if i==0 else ('StaticGapCheckA.'if i==3 else '')
  prevcount=549 if i==0 else chunks[i-1][3]
  s+=f'''theorem exact_{k}_source_indices :
    StaticGapData.forward{k}.map Row.sourceIndex = List.range' {raw} {n} ∧
    StaticGapData.backward{k}.map Row.sourceIndex = List.range' {raw} {n} := by
  decide +kernel

'''
  for d in ('forward','backward'):
   rows=f'StaticGapData.{d}{k}'; ev=f'({rows}.map Row.event)'
   s+=f'''theorem {d}_{k}_labels_checked :
    CheckDecomposition.labelRowsB {rows} {prevlabel} = true := by
  decide +kernel

theorem {d}_{k}_children_checked :
    CheckDecomposition.childRowsB PilotData.data {rows} = true := by
  decide +kernel

theorem {d}_{k}_checked :
    checkRows PilotData.data {rows} {prevlabel} = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨{d}_{k}_labels_checked, {d}_{k}_children_checked⟩

theorem {d}_{k}_wellLabelled :
    LemmaG.Stream.WellLabelled {ev} {prevlabel} :=
  checkRows_wellLabelled PilotData.data {rows}
    {prevlabel} {d}_{k}_checked

theorem {d}_support{end} :
    {ev}.all (Boundary192.supportedB StaticGapData.new{end}) = true := by
  decide +kernel

theorem {d}_touched{end} :
    StaticGapData.new{end}.all (fun r =>
      LemmaG.Stream.labRun {ev} {prevlabel} r == (7 : FrameLabel)) = true := by
  rfl

theorem {d}_checkpoint{end} :
    LemmaG.Stream.labRun {ev} {prevlabel} = StaticGapData.labels{end} :=
  SparseValues.sparse_checkpoint {rows} {prevlabel}
    (fun _ => (7 : FrameLabel)) StaticGapData.new{end} {d}_support{end} {d}_touched{end}

theorem {d}_composed_wellLabelled{end} :
    LemmaG.Stream.WellLabelled {pref(d,i)}
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨{prevns}{d}_composed_wellLabelled{prevcount}, ?_⟩
  rw [{prevns}{d}_composed_checkpoint{prevcount}]
  exact {d}_{k}_wellLabelled

theorem {d}_composed_checkpoint{end} :
    LemmaG.Stream.labRun {pref(d,i)}
      (initialLabels PilotData.data) = StaticGapData.labels{end} := by
  rw [List.map_append, LemmaG.Stream.labRun_append, {prevns}{d}_composed_checkpoint{prevcount}]
  exact {d}_checkpoint{end}

'''
 probes=re.findall(r'^theorem (\w+)',s,re.M);assert len(probes)==57
 s+='\n'.join('#print axioms '+x for x in probes)+f'\nend CurrentMain.F19SelectedCoverage.{name}\n'
 path=out/f'F19Coverage{name}.lean';assert not path.exists();path.write_text(s)
