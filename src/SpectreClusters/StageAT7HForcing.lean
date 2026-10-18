module

public import SpectreClusters.StageAActualSupport
public import SpectreClusters.StageAT7HForcingData

@[expose] public section


/-! Radius-two forcing of the seventh hat from the final Stage A rows.
No enumeration of T6H coronas is needed: the indicated genuine neighbor
has exactly two surviving supports, each containing the required hat. -/
namespace SpectreClusters.StageA

theorem turtle_special_owns_seventh (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f)
    (hr : RootOwned f (canonicalRoot .turtle))
    (hword : rawWordAt .turtle 0 = wordOf f .turtle) :
    RootOwned f seventhHat := by
  obtain ⟨j,hj,hjword,hs⟩ := actual_neighbor_support hcaptures f hf .turtle hr 0 3
    hword turtle_core_hat_mem turtle_core_hat_alignment
  have hsplit : j = 6 ∨ j = 8 := turtle_core_hat_support j hj hs
  have hm : 1 ∈ rawWordAt .hat j := by
    rcases hsplit with rfl | rfl
    · exact turtle_support6_extra_mem
    · exact turtle_support8_extra_mem
  have hp : RootOwned (normalizeField f (candidateAt .turtle 3)) (candidateAt .hat 1) := by
    apply GridReductionWindowBinding.represented_neighbor_owned
      (normalizeField f (candidateAt .turtle 3))
      (normalizeField_valid f hf (candidateAt .turtle 3)) .hat
    · apply field_mem_candidates
      · exact normalizeField_valid f hf (candidateAt .turtle 3)
      · apply normalizeField_rootOwned
        exact GridReductionWindowBinding.represented_neighbor_owned f hf .turtle
          (field_mem_candidates f hf .turtle hr) 3 (show 3 ∈ wordOf f .turtle from hword ▸ turtle_core_hat_mem)
    · change 1 ∈ wordOf (normalizeField f (candidateAt .turtle 3)) .hat
      change rawWordAt .hat j = wordOf (normalizeField f (candidateAt .turtle 3)) .hat at hjword
      exact hjword ▸ hm
  have howned := owned_of_normalized_owned f (candidateAt .turtle 3) (candidateAt .hat 1) hp
  simpa only [turtle_seventh_pose] using howned

/-- Every exceptional turtle occurrence owns exactly the listed T7H tile
poses as a subpatch. Pairwise cluster uniqueness is a separate conclusion. -/
theorem turtle_special_owns_t7h (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) (hr : RootOwned f root) (hk : root.kind = .turtle)
    (hword : rawWordAt .turtle 0 = wordOf (normalizeField f root) .turtle) :
    ClusterOwned f .t7h root := by
  have hcore := turtle_special_owns_t6h f hf root hr hk hword
  have hroot : RootOwned (normalizeField f root) (canonicalRoot .turtle) := by
    simpa only [hk,originRoot,canonicalRoot] using normalizeField_rootOwned f root hr
  have hextra := owned_of_normalized_owned f root seventhHat
    (turtle_special_owns_seventh hcaptures (normalizeField f root)
      (normalizeField_valid f hf root) hroot hword)
  refine ⟨hk,?_⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  rcases t7h_member_core_or_extra q hq with hcoreq | rfl
  · exact hcore.2 _ (List.mem_map.mpr ⟨q,hcoreq,rfl⟩)
  · exact hextra

end SpectreClusters.StageA
