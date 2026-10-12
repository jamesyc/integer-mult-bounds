import CurrentR420BoundaryData

/-! Current-source finite decoder/domain and B-band certificate only.
The 597 source writes mean that B does not preserve every non-target register.
No-target operands support the already accepted generic target-translation
law, but this file does not yet instantiate the XOR execution theorem.
A/C cleanup, D compensation, scalar COPY lifecycle, physical frame realization
and the all-size cost theorem remain separate. In a later lifecycle model,
temporary660 is overwritten then cleared; arbitrary dirty restoration is absent. -/
namespace CurrentMain.CurrentR420Boundary
open Data
set_option Elab.async false

theorem selected_shape :
    h = 8 ∧ v = 120 ∧ R = 420 ∧ registers = 660 ∧
    format = "bitE8/1+mut" ∧ form = "<x,y>/2" ∧ coords = "ham" := by decide +kernel

theorem line_shape :
    lines.length = 120 ∧ lines.all (fun row => row.length == 8) = true :=
  SelectedBitCarrierBoundary.line_shape

theorem frame_index_permutation :
    (frameOrder.map Fin.val).mergeSort (fun a b => decide (a ≤ b)) = List.range 672 := by
  decide +kernel

theorem frame_domain : frames.length = 672 ∧
    frames.all (fun row => row.all (fun i => decide (i < 120))) = true := by decide +kernel

theorem zero_full_rows : frames[0]? = some [] ∧
    frames[1]? = some (List.range 120) := by decide +kernel

theorem boundary_domain : start.length = 660 ∧ final.length = 660 ∧
    start.all (fun f => decide (f < 672)) = true ∧
    final.all (fun f => decide (f < 672)) = true := by decide +kernel

theorem source_entrances : (List.range 120).all (fun r =>
    match start[r]? with
    | none => false
    | some f => frames[f]? == some [r]) = true := by decide +kernel

theorem nonsource_entrances : start.drop 120 = List.replicate 540 0 := by decide +kernel

theorem source_helper_final_full : final.take 120 = List.replicate 120 1 ∧
    final.drop 240 = List.replicate 420 1 := by decide +kernel

theorem retained_helper_ids : ret.length = 9 ∧ ret.Nodup ∧
    ret.all (fun r => decide (240 ≤ r ∧ r < 660)) = true := by decide +kernel

theorem phase_shape : phaseB.length = 837 ∧
    (phaseB.map (fun g => g.2.2.length)).foldl Nat.add 0 = 1077 := by decide +kernel

theorem phase_domains : phaseB.all (fun g =>
    decide (g.1 < 672 ∧ g.2.1 < 660) &&
    g.2.2.all (fun r => decide (r < 660))) = true := by decide +kernel

theorem band_order : phaseB = firstTargets ++ sourceMiddle ++ lastTargets := rfl

theorem band_lengths : firstTargets.length = 120 ∧ sourceMiddle.length = 597 ∧
    lastTargets.length = 120 := by decide +kernel

theorem first_target_band : firstTargets.all (fun g =>
    decide (120 ≤ g.2.1 ∧ g.2.1 < 240 ∧ g.2.2.length = 1) &&
    g.2.2.all (fun r => decide (r < 120))) = true := by decide +kernel

theorem middle_source_band : sourceMiddle.all (fun g =>
    decide (g.2.1 < 120 ∧ g.2.2.length = 1)) = true := by decide +kernel

theorem middle_operand_bands :
    (sourceMiddle.take 477).all (fun g => g.2.2.all (fun r => decide (r < 120))) = true ∧
    (sourceMiddle.drop 477).length = 120 ∧
    (sourceMiddle.drop 477).all (fun g => g.2.2.all (fun r => decide (240 ≤ r))) = true := by
  decide +kernel

theorem last_target_band : lastTargets.all (fun g =>
    decide (120 ≤ g.2.1 ∧ g.2.1 < 240 ∧ g.2.2.length = 3) &&
    g.2.2.all (fun r => decide (r < 120))) = true := by decide +kernel

theorem final_target_frames : lastTargets.all (fun g =>
    final[g.2.1]? == some g.1) = true := by decide +kernel

theorem no_target_operands : phaseB.all (fun g =>
    g.2.2.all (fun r => decide (r < 120 ∨ 240 ≤ r))) = true := by decide +kernel

theorem no_self_reads : phaseB.all (fun g =>
    g.2.2.all (fun r => decide (r ≠ g.2.1))) = true := by decide +kernel

theorem scatter_shape : scatter.length = 120 ∧
    (scatter.map List.length).foldl Nat.add 0 = 568 := by decide +kernel

theorem scatter_index_domain : scatter.all (fun row =>
    row.all (fun k => decide (k < ret.length))) = true := by decide +kernel

theorem scatter_helpers : scatter.all (fun row => row.all (fun k =>
    match ret[k]? with
    | none => false
    | some r => decide (240 ≤ r ∧ r < 660))) = true := by decide +kernel

theorem temporary_index : temporary.val = 660 ∧ temporary.val < 661 := by decide +kernel

theorem embed_preserves_index (r : Reg) : (embed r).val = r.val := rfl

theorem original_excludes_temporary (r : Reg) : embed r ≠ temporary := by
  intro h
  have hv : r.val = 660 := congrArg Fin.val h
  exact (Nat.ne_of_lt r.isLt) hv

end CurrentMain.CurrentR420Boundary
#print axioms CurrentMain.CurrentR420Boundary.selected_shape
#print axioms CurrentMain.CurrentR420Boundary.line_shape
#print axioms CurrentMain.CurrentR420Boundary.frame_index_permutation
#print axioms CurrentMain.CurrentR420Boundary.frame_domain
#print axioms CurrentMain.CurrentR420Boundary.zero_full_rows
#print axioms CurrentMain.CurrentR420Boundary.boundary_domain
#print axioms CurrentMain.CurrentR420Boundary.source_entrances
#print axioms CurrentMain.CurrentR420Boundary.nonsource_entrances
#print axioms CurrentMain.CurrentR420Boundary.source_helper_final_full
#print axioms CurrentMain.CurrentR420Boundary.retained_helper_ids
#print axioms CurrentMain.CurrentR420Boundary.phase_shape
#print axioms CurrentMain.CurrentR420Boundary.phase_domains
#print axioms CurrentMain.CurrentR420Boundary.band_order
#print axioms CurrentMain.CurrentR420Boundary.band_lengths
#print axioms CurrentMain.CurrentR420Boundary.first_target_band
#print axioms CurrentMain.CurrentR420Boundary.middle_source_band
#print axioms CurrentMain.CurrentR420Boundary.middle_operand_bands
#print axioms CurrentMain.CurrentR420Boundary.last_target_band
#print axioms CurrentMain.CurrentR420Boundary.final_target_frames
#print axioms CurrentMain.CurrentR420Boundary.no_target_operands
#print axioms CurrentMain.CurrentR420Boundary.no_self_reads
#print axioms CurrentMain.CurrentR420Boundary.scatter_shape
#print axioms CurrentMain.CurrentR420Boundary.scatter_index_domain
#print axioms CurrentMain.CurrentR420Boundary.scatter_helpers
#print axioms CurrentMain.CurrentR420Boundary.temporary_index
#print axioms CurrentMain.CurrentR420Boundary.embed_preserves_index
#print axioms CurrentMain.CurrentR420Boundary.original_excludes_temporary
