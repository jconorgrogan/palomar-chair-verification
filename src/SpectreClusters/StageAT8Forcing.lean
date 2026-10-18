module

public import SpectreClusters.StageAActualSupport
public import SpectreClusters.StageAT7HForcing
public import SpectreClusters.StageAT8ForcingData

@[expose] public section


/-! Radius-two forcing of the eighth hat from the final Stage A rows.
No enumeration of larger composite coronas is needed: the indicated genuine neighbor
has exactly two surviving supports, each containing the required hat. -/
namespace SpectreClusters.StageA

theorem turtle_special_owns_eighth (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f)
    (hr : RootOwned f (canonicalRoot .turtle))
    (hword : rawWordAt .turtle 0 = wordOf f .turtle) :
    RootOwned f eighthHat := by
  obtain ⟨j,hj,hjword,hs⟩ := actual_neighbor_support hcaptures f hf .turtle hr 0 11
    hword turtle_upper_hat_mem turtle_upper_hat_alignment
  have hsplit : j = 13 ∨ j = 15 := turtle_upper_hat_support j hj hs
  have hm : 1 ∈ rawWordAt .hat j := by
    rcases hsplit with rfl | rfl
    · exact turtle_support13_extra_mem
    · exact turtle_support15_extra_mem
  have hp : RootOwned (normalizeField f (candidateAt .turtle 11)) (candidateAt .hat 1) := by
    apply GridReductionWindowBinding.represented_neighbor_owned
      (normalizeField f (candidateAt .turtle 11))
      (normalizeField_valid f hf (candidateAt .turtle 11)) .hat
    · apply field_mem_candidates
      · exact normalizeField_valid f hf (candidateAt .turtle 11)
      · apply normalizeField_rootOwned
        exact GridReductionWindowBinding.represented_neighbor_owned f hf .turtle
          (field_mem_candidates f hf .turtle hr) 11 (show 11 ∈ wordOf f .turtle from hword ▸ turtle_upper_hat_mem)
    · change 1 ∈ wordOf (normalizeField f (candidateAt .turtle 11)) .hat
      change rawWordAt .hat j = wordOf (normalizeField f (candidateAt .turtle 11)) .hat at hjword
      exact hjword ▸ hm
  have howned := owned_of_normalized_owned f (candidateAt .turtle 11) (candidateAt .hat 1) hp
  simpa only [turtle_eighth_pose] using howned

/-- Every exceptional turtle owns the literal T8H footprint. The eighth
hat may belong to a different T7H core, so this is not yet an assignment
of disjoint T8H clusters. -/
theorem turtle_special_owns_t8h_footprint (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) (hr : RootOwned f root) (hk : root.kind = .turtle)
    (hword : rawWordAt .turtle 0 = wordOf (normalizeField f root) .turtle) :
    ClusterOwned f .t8h root := by
  have hcore := turtle_special_owns_t7h hcaptures f hf root hr hk hword
  have hroot : RootOwned (normalizeField f root) (canonicalRoot .turtle) := by
    simpa only [hk,originRoot,canonicalRoot] using normalizeField_rootOwned f root hr
  have hextra := owned_of_normalized_owned f root eighthHat
    (turtle_special_owns_eighth hcaptures (normalizeField f root)
      (normalizeField_valid f hf root) hroot hword)
  refine ⟨hk,?_⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  rcases t8h_member_core_or_extra q hq with hcoreq | rfl
  · exact hcore.2 _ (List.mem_map.mpr ⟨q,hcoreq,rfl⟩)
  · exact hextra

end SpectreClusters.StageA
