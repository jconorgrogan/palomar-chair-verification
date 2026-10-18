module

public import SpectreClusters.StageDRawHaloT7HWitnesses
public import SpectreClusters.StageDRawHaloT7HRange0
public import SpectreClusters.StageDRawHaloT7HRange1
public import SpectreClusters.StageDRawHaloT7HRange2
public import SpectreClusters.StageDRawHaloT7HRange3
public import SpectreClusters.StageDRawHaloT7HRange4
public import SpectreClusters.StageDRawHaloT7HRange5
public import SpectreClusters.StageDRawHaloT7HRange6
public import SpectreClusters.StageDRawHaloT7HRange7
public import SpectreClusters.StageDRawHaloT7HRange8
public import SpectreClusters.StageDRawHaloT7HRange9
public import SpectreClusters.StageDRawHaloT8HWitnesses
public import SpectreClusters.StageDRawHaloT8HRange0
public import SpectreClusters.StageDRawHaloT8HRange1
public import SpectreClusters.StageDRawHaloT8HRange2
public import SpectreClusters.StageDRawHaloT8HRange3
public import SpectreClusters.StageDRawHaloT8HRange4
public import SpectreClusters.StageDRawHaloT8HRange5
public import SpectreClusters.StageDRawHaloT8HRange6
public import SpectreClusters.StageDRawHaloT8HRange7
public import SpectreClusters.StageDRawHaloT8HRange8
public import SpectreClusters.StageDRawHaloT8HRange9

@[expose] public section

namespace SpectreClusters.StageD.Raw
theorem haloT7H_raw_binding (c : Cell) : c ∈ halo (clusterCells .t7h) ↔ c ∈ haloOrder .t7h := by
  constructor
  · intro hc
    apply halo_subset_of_ranges _ _ (by decide) ?_ c hc
    intro b
    rcases b with ⟨b,hb⟩
    have hcases : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact haloT7HRange0_checked
    · exact haloT7HRange1_checked
    · exact haloT7HRange2_checked
    · exact haloT7HRange3_checked
    · exact haloT7HRange4_checked
    · exact haloT7HRange5_checked
    · exact haloT7HRange6_checked
    · exact haloT7HRange7_checked
    · exact haloT7HRange8_checked
    · exact haloT7HRange9_checked
  · intro hc
    rw [←haloWitnessesT7H_domain] at hc
    exact haloWitnesses_sound _ _ haloWitnessesT7H_checked c hc
theorem haloT8H_raw_binding (c : Cell) : c ∈ halo (clusterCells .t8h) ↔ c ∈ haloOrder .t8h := by
  constructor
  · intro hc
    apply halo_subset_of_ranges _ _ (by decide) ?_ c hc
    intro b
    rcases b with ⟨b,hb⟩
    have hcases : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact haloT8HRange0_checked
    · exact haloT8HRange1_checked
    · exact haloT8HRange2_checked
    · exact haloT8HRange3_checked
    · exact haloT8HRange4_checked
    · exact haloT8HRange5_checked
    · exact haloT8HRange6_checked
    · exact haloT8HRange7_checked
    · exact haloT8HRange8_checked
    · exact haloT8HRange9_checked
  · intro hc
    rw [←haloWitnessesT8H_domain] at hc
    exact haloWitnesses_sound _ _ haloWitnessesT8H_checked c hc
theorem halo_interpretation_binding_certified (k : ClusterKind) (hk : LegalClusterKind k) (c : Cell) :
    c ∈ halo (clusterCells k) ↔ c ∈ StageD.haloOrder k := by
  rw [interpretation_order_eq_reverse,List.mem_reverse]
  rcases hk with rfl | rfl
  · exact haloT7H_raw_binding c
  · exact haloT8H_raw_binding c
end SpectreClusters.StageD.Raw
