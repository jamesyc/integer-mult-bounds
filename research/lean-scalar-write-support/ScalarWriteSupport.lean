import PR516Realize

/-!
Generic destination-support preservation for accepted PR509 event semantics,
reusing PR516 LemmaA.dst and phys_ne. No new realization or conjugation proof.
The optional source witness below is historical selected PR596 at main5996.
Its exact forward raw1..9168 destination projection has224 constant-target runs,
all in L112..L223. The supplied typed-word trace equality remains explicit;
this is not a full-prefix decoder or Python/physical executor theorem.
The sixteen entry adapters and residual R-inverse/hstart obligations are separate.
Apache-2.0. PR509/PR516 upstream attribution retained. OpenAI-assisted.
-/
set_option Elab.async false

namespace CurrentMain.ScalarWriteSupport
open LemmaG LemmaG.Stream

section Generic
variable {ι Λ K M : Type*} [DecidableEq ι] [Semiring K]
  [AddCommMonoid M] [Module K M]

/-- A destination-disjoint register is unchanged by the interpreted event run. -/
theorem physRun_unchanged (rec : Λ → Λ → M → M)
    (es : List (Event ι Λ K)) (h : ι → M) (i : ι)
    (hs : ∀ e ∈ es, i ≠ LemmaA.dst e) :
    physRun rec es h i = h i := by
  induction es generalizing h with
  | nil => rfl
  | cons e es ih =>
      change physRun rec es (e.phys rec h) i = h i
      rw [ih (e.phys rec h) (fun e' he' => hs e' (List.mem_cons_of_mem e he'))]
      exact LemmaA.phys_ne rec e h i (hs e (List.mem_cons_self))

/-- The same support law for the accepted scalar shadow. -/
theorem scalRun_unchanged (es : List (Event ι Λ K)) (h : ι → M) (i : ι)
    (hs : ∀ e ∈ es, i ≠ LemmaA.dst e) : scalRun es h i = h i :=
  physRun_unchanged (fun _ _ v => v) es h i hs
end Generic

/-- Compressed destinations, independent of coefficient values or event execution. -/
def expandTargets (runs : List (Fin 112 × Nat)) : List Nat :=
  runs.flatMap (fun r => List.replicate r.2 (112 + r.1.val))

theorem expanded_target_lt (runs : List (Fin 112 × Nat))
    (t : Nat) (ht : t ∈ expandTargets runs) : t < 224 := by
  obtain ⟨r, _, hm⟩ := List.mem_flatMap.mp ht
  have he : t = 112 + r.1.val := List.eq_of_mem_replicate hm
  rw [he]
  exact Nat.add_lt_add_left r.1.isLt 112

namespace Historical596
/-- Exact source-ordered run-length encoding; indices are offset by112. -/
def targetRuns : List (Fin 112 × Nat) := [
  (⟨7, by decide⟩, 2),
  (⟨57, by decide⟩, 1),
  (⟨27, by decide⟩, 2),
  (⟨0, by decide⟩, 1),
  (⟨81, by decide⟩, 2),
  (⟨92, by decide⟩, 1),
  (⟨87, by decide⟩, 2),
  (⟨76, by decide⟩, 1),
  (⟨10, by decide⟩, 2),
  (⟨62, by decide⟩, 1),
  (⟨91, by decide⟩, 2),
  (⟨70, by decide⟩, 1),
  (⟨11, by decide⟩, 2),
  (⟨63, by decide⟩, 1),
  (⟨90, by decide⟩, 2),
  (⟨71, by decide⟩, 1),
  (⟨79, by decide⟩, 2),
  (⟨94, by decide⟩, 1),
  (⟨89, by decide⟩, 2),
  (⟨72, by decide⟩, 1),
  (⟨9, by decide⟩, 2),
  (⟨61, by decide⟩, 1),
  (⟨25, by decide⟩, 2),
  (⟨2, by decide⟩, 1),
  (⟨38, by decide⟩, 2),
  (⟨17, by decide⟩, 1),
  (⟨31, by decide⟩, 2),
  (⟨12, by decide⟩, 1),
  (⟨77, by decide⟩, 2),
  (⟨103, by decide⟩, 1),
  (⟨56, by decide⟩, 2),
  (⟨100, by decide⟩, 1),
  (⟨19, by decide⟩, 2),
  (⟨40, by decide⟩, 1),
  (⟨55, by decide⟩, 2),
  (⟨101, by decide⟩, 1),
  (⟨39, by decide⟩, 2),
  (⟨18, by decide⟩, 1),
  (⟨102, by decide⟩, 2),
  (⟨54, by decide⟩, 1),
  (⟨24, by decide⟩, 2),
  (⟨107, by decide⟩, 1),
  (⟨85, by decide⟩, 2),
  (⟨98, by decide⟩, 1),
  (⟨35, by decide⟩, 2),
  (⟨45, by decide⟩, 1),
  (⟨32, by decide⟩, 2),
  (⟨48, by decide⟩, 1),
  (⟨109, by decide⟩, 2),
  (⟨22, by decide⟩, 1),
  (⟨33, by decide⟩, 2),
  (⟨49, by decide⟩, 1),
  (⟨23, by decide⟩, 2),
  (⟨108, by decide⟩, 1),
  (⟨50, by decide⟩, 2),
  (⟨34, by decide⟩, 1),
  (⟨28, by decide⟩, 2),
  (⟨58, by decide⟩, 1),
  (⟨1, by decide⟩, 2),
  (⟨6, by decide⟩, 1),
  (⟨86, by decide⟩, 2),
  (⟨93, by decide⟩, 1),
  (⟨75, by decide⟩, 2),
  (⟨82, by decide⟩, 1),
  (⟨60, by decide⟩, 2),
  (⟨30, by decide⟩, 1),
  (⟨74, by decide⟩, 2),
  (⟨83, by decide⟩, 1),
  (⟨29, by decide⟩, 2),
  (⟨59, by decide⟩, 1),
  (⟨84, by decide⟩, 2),
  (⟨73, by decide⟩, 1),
  (⟨66, by decide⟩, 2),
  (⟨95, by decide⟩, 1),
  (⟨88, by decide⟩, 2),
  (⟨80, by decide⟩, 1),
  (⟨26, by decide⟩, 2),
  (⟨8, by decide⟩, 1),
  (⟨3, by decide⟩, 2),
  (⟨67, by decide⟩, 1),
  (⟨97, by decide⟩, 2),
  (⟨64, by decide⟩, 1),
  (⟨4, by decide⟩, 2),
  (⟨68, by decide⟩, 1),
  (⟨65, by decide⟩, 2),
  (⟨96, by decide⟩, 1),
  (⟨69, by decide⟩, 2),
  (⟨5, by decide⟩, 1),
  (⟨105, by decide⟩, 2),
  (⟨42, by decide⟩, 1),
  (⟨53, by decide⟩, 2),
  (⟨15, by decide⟩, 1),
  (⟨106, by decide⟩, 2),
  (⟨41, by decide⟩, 1),
  (⟨52, by decide⟩, 2),
  (⟨14, by decide⟩, 1),
  (⟨44, by decide⟩, 2),
  (⟨16, by decide⟩, 1),
  (⟨51, by decide⟩, 2),
  (⟨13, by decide⟩, 1),
  (⟨104, by decide⟩, 2),
  (⟨43, by decide⟩, 1),
  (⟨99, by decide⟩, 2),
  (⟨78, by decide⟩, 1),
  (⟨46, by decide⟩, 2),
  (⟨20, by decide⟩, 1),
  (⟨111, by decide⟩, 2),
  (⟨36, by decide⟩, 1),
  (⟨110, by decide⟩, 2),
  (⟨37, by decide⟩, 1),
  (⟨47, by decide⟩, 2),
  (⟨21, by decide⟩, 1),
  (⟨6, by decide⟩, 71),
  (⟨82, by decide⟩, 71),
  (⟨75, by decide⟩, 72),
  (⟨1, by decide⟩, 76),
  (⟨93, by decide⟩, 77),
  (⟨58, by decide⟩, 77),
  (⟨28, by decide⟩, 70),
  (⟨86, by decide⟩, 74),
  (⟨12, by decide⟩, 73),
  (⟨100, by decide⟩, 73),
  (⟨56, by decide⟩, 78),
  (⟨31, by decide⟩, 73),
  (⟨103, by decide⟩, 73),
  (⟨17, by decide⟩, 73),
  (⟨38, by decide⟩, 75),
  (⟨77, by decide⟩, 70),
  (⟨72, by decide⟩, 73),
  (⟨2, by decide⟩, 73),
  (⟨25, by decide⟩, 73),
  (⟨89, by decide⟩, 73),
  (⟨61, by decide⟩, 71),
  (⟨94, by decide⟩, 71),
  (⟨79, by decide⟩, 71),
  (⟨9, by decide⟩, 71),
  (⟨70, by decide⟩, 78),
  (⟨71, by decide⟩, 78),
  (⟨90, by decide⟩, 79),
  (⟨91, by decide⟩, 77),
  (⟨63, by decide⟩, 76),
  (⟨62, by decide⟩, 76),
  (⟨10, by decide⟩, 77),
  (⟨11, by decide⟩, 75),
  (⟨101, by decide⟩, 74),
  (⟨54, by decide⟩, 74),
  (⟨102, by decide⟩, 79),
  (⟨55, by decide⟩, 73),
  (⟨18, by decide⟩, 74),
  (⟨40, by decide⟩, 74),
  (⟨19, by decide⟩, 76),
  (⟨39, by decide⟩, 70),
  (⟨83, by decide⟩, 71),
  (⟨73, by decide⟩, 71),
  (⟨84, by decide⟩, 77),
  (⟨74, by decide⟩, 73),
  (⟨59, by decide⟩, 77),
  (⟨30, by decide⟩, 77),
  (⟨60, by decide⟩, 75),
  (⟨29, by decide⟩, 71),
  (⟨36, by decide⟩, 123),
  (⟨21, by decide⟩, 123),
  (⟨47, by decide⟩, 111),
  (⟨111, by decide⟩, 111),
  (⟨37, by decide⟩, 123),
  (⟨20, by decide⟩, 123),
  (⟨46, by decide⟩, 109),
  (⟨110, by decide⟩, 109),
  (⟨0, by decide⟩, 111),
  (⟨76, by decide⟩, 111),
  (⟨87, by decide⟩, 109),
  (⟨27, by decide⟩, 107),
  (⟨92, by decide⟩, 109),
  (⟨57, by decide⟩, 109),
  (⟨7, by decide⟩, 107),
  (⟨81, by decide⟩, 105),
  (⟨98, by decide⟩, 74),
  (⟨48, by decide⟩, 74),
  (⟨32, by decide⟩, 71),
  (⟨85, by decide⟩, 75),
  (⟨45, by decide⟩, 68),
  (⟨107, by decide⟩, 68),
  (⟨24, by decide⟩, 68),
  (⟨35, by decide⟩, 72),
  (⟨80, by decide⟩, 73),
  (⟨67, by decide⟩, 73),
  (⟨3, by decide⟩, 80),
  (⟨88, by decide⟩, 75),
  (⟨8, by decide⟩, 80),
  (⟨95, by decide⟩, 80),
  (⟨66, by decide⟩, 78),
  (⟨26, by decide⟩, 73),
  (⟨13, by decide⟩, 78),
  (⟨78, by decide⟩, 78),
  (⟨99, by decide⟩, 79),
  (⟨51, by decide⟩, 79),
  (⟨43, by decide⟩, 78),
  (⟨16, by decide⟩, 78),
  (⟨44, by decide⟩, 77),
  (⟨104, by decide⟩, 77),
  (⟨15, by decide⟩, 83),
  (⟨14, by decide⟩, 83),
  (⟨52, by decide⟩, 85),
  (⟨53, by decide⟩, 83),
  (⟨41, by decide⟩, 83),
  (⟨42, by decide⟩, 83),
  (⟨105, by decide⟩, 83),
  (⟨106, by decide⟩, 81),
  (⟨68, by decide⟩, 72),
  (⟨5, by decide⟩, 72),
  (⟨69, by decide⟩, 79),
  (⟨4, by decide⟩, 73),
  (⟨96, by decide⟩, 79),
  (⟨64, by decide⟩, 79),
  (⟨97, by decide⟩, 77),
  (⟨65, by decide⟩, 71),
  (⟨49, by decide⟩, 74),
  (⟨34, by decide⟩, 74),
  (⟨50, by decide⟩, 76),
  (⟨33, by decide⟩, 72),
  (⟨108, by decide⟩, 68),
  (⟨22, by decide⟩, 68),
  (⟨109, by decide⟩, 73),
  (⟨23, by decide⟩, 69)
]

def targetTrace : List Nat := expandTargets targetRuns

/-- Count the224 encoded runs, without unfolding a9168-step scalar execution. -/
theorem encoded_event_count : (targetRuns.map Prod.snd).sum = 9168 := by
  decide +kernel

def first33Support : List (Fin 736) := [558, 559, 560, 561, 570, 571, 572, 573, 582, 583, 584, 585, 594, 595, 596, 597]

theorem support_above_targets :
    ∀ r ∈ first33Support, 224 ≤ r.val := by
  decide +kernel

/-- Explicit destination-trace correspondence is a caller-supplied typed-prefix
obligation. Coefficients, labels and the physical executor are not reconstructed. -/
def HasSourceWriteTrace {Λ K : Type*} (es : List (Event (Fin 736) Λ K)) : Prop :=
  es.map (fun e => (LemmaA.dst e).val) = targetTrace

section Semantics
variable {Λ K M : Type*} [Semiring K] [AddCommMonoid M] [Module K M]

theorem forward_support_preserved (es : List (Event (Fin 736) Λ K))
    (htrace : HasSourceWriteTrace es) (h : Fin 736 → M)
    (r : Fin 736) (hr : r ∈ first33Support) : scalRun es h r = h r := by
  apply scalRun_unchanged es h r
  intro e he heq
  have hm : (LemmaA.dst e).val ∈ targetTrace := by
    rw [← htrace]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have ht := expanded_target_lt targetRuns (LemmaA.dst e).val hm
  have hge := support_above_targets r hr
  cases heq
  exact (Nat.not_lt_of_ge hge) ht
end Semantics
end Historical596
end CurrentMain.ScalarWriteSupport

#print axioms CurrentMain.ScalarWriteSupport.physRun_unchanged
#print axioms CurrentMain.ScalarWriteSupport.scalRun_unchanged
#print axioms CurrentMain.ScalarWriteSupport.expanded_target_lt
#print axioms CurrentMain.ScalarWriteSupport.Historical596.encoded_event_count
#print axioms CurrentMain.ScalarWriteSupport.Historical596.support_above_targets
#print axioms CurrentMain.ScalarWriteSupport.Historical596.forward_support_preserved
#check @CurrentMain.ScalarWriteSupport.Historical596.forward_support_preserved
