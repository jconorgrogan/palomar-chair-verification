module

public import SpectreClusters.StageABoundComplete
public import SpectreClusters.StageAReductionChecks
public import SpectreClusters.StageALocalClaims

@[expose] public section


/-! Complete discrete stage A. Every normalized occurrence in every coherent
covering of the entire kite grid belongs to the literal23-row survivor
family, via checked finite enumeration and checked occurrence-preserving
rejections. No assertion of physical registration or later clustering. -/
namespace SpectreClusters.StageA

theorem captures_two :
    GridReductionWindows.Captures rawWordAt (keptIds 2)
      GridReductionWindowBinding.encode :=
  GridReductionWindowBinding.captures_two field_mem_candidates
    grid_word_mem_rawWords stage0_checked stage1_checked

/-- Every original row ID representing the actual field survives both
checked reductions. This preserves occurrence identity, not just existence
of some possibly duplicate final word. -/
theorem actual_id_survives_two (f : Cell → HTPlacement) (hf : ValidGridField f)
    (kind : HTKind) (hr : RootOwned f (canonicalRoot kind)) (i : Nat)
    (hi : i ∈ keptIds 0 kind) (hword : rawWordAt kind i = wordOf f kind) :
    i ∈ keptIds 2 kind := by
  have hzero := GridReductionWindowBinding.captures_zero grid_word_mem_rawWords
  have hone := GridReductionWindowBinding.captures_next 0 field_mem_candidates
    hzero stage0_checked
  have hi1 := GridReductionWindowBinding.retains_actual_id 0 field_mem_candidates
    hzero stage0_checked f hf kind hr i hi hword
  exact GridReductionWindowBinding.retains_actual_id 1 field_mem_candidates
    hone stage1_checked f hf kind hr i hi1 hword

theorem normalized_occurrence_survives (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) (hr : RootOwned f root) :
    ∃ i ∈ keptIds 2 root.kind,
      rawWordAt root.kind i = wordOf (normalizeField f root) root.kind := by
  exact GridReductionWindowBinding.normalized_mem_two field_mem_candidates
    grid_word_mem_rawWords stage0_checked stage1_checked f hf root hr

theorem final_word_count (kind : HTKind) : (keptIds 2 kind).length = 23 := by
  cases kind <;> rfl

end SpectreClusters.StageA
