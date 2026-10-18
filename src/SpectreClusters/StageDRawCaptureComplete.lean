module

public import SpectreClusters.StageDRawSelectedWords
public import SpectreClusters.StageDRawProbeSelectionsT7H
public import SpectreClusters.StageDRawProbeSelectionsT8H
public import SpectreClusters.StageDRawProbePruningT7H
public import SpectreClusters.StageDRawProbePruningT8H
public import SpectreClusters.StageDRawProbeRowsT7H
public import SpectreClusters.StageDRawProbeRowsT8H

@[expose] public section

namespace SpectreClusters.StageD.Raw
theorem selectedProbeWordT7H (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t7h)) : ∃ w : List Nat,
      FiniteCoverWords.OverChoices w (probeChoices .t7h) ∧
      w.Pairwise (fun a b => idCompatible .t7h a b = true) ∧
      ∀ a ∈ w, ClusterRootOwned f ((candidateList .t7h).getD a fallback) := by
  classical
  let chosen : Nat → Nat := fun j => if hj : j < 6 then
    Classical.choose (probeSelectionsT7H f hf hr j hj) else 0
  have hchosen (j : Nat) (hj : j < 6) :
      chosen j ∈ (probeChoices .t7h).getD j [] ∧
      chosen j < (candidateList .t7h).length ∧
      (candidateList .t7h).getD (chosen j) fallback =
        f ((probeCells .t7h).getD j ⟨(0,0),0⟩) := by
    dsimp only [chosen]
    rw [dif_pos hj]
    exact Classical.choose_spec (probeSelectionsT7H f hf hr j hj)
  have hcompatible (i : Nat) (hi : i < 6) (j : Nat) (hj : j < 6) :
      (candidateList .t7h).getD (chosen i) fallback = (candidateList .t7h).getD (chosen j) fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList .t7h).getD (chosen i) fallback))
        (clusterPlacementCells ((candidateList .t7h).getD (chosen j) fallback)) := by
    rw [(hchosen i hi).2.2,(hchosen j hj).2.2]
    exact clusterField_compatible f hf _ _
  have hdomain := IndexedPruning.probePruneT7H_domain chosen
    (fun i hi => (hchosen i hi).1) hcompatible
  refine ⟨selectedIndexWord 6 chosen,
    selectedIndexWord_overChoices 6 chosen (probeChoices .t7h) (by rfl)
      (fun i hi => (hchosen i hi).1),?_,?_⟩
  · exact selectedIndexWord_pairwise .t7h 6 chosen (fun i hi j hj =>
      reducedCompatibilityT7H_sound (chosen i) (chosen j)
        (hdomain i hi) (hdomain j hj) (hcompatible i hi j hj))
  · apply selectedIndexWord_owned f .t7h 6 chosen
    intro i hi
    rw [(hchosen i hi).2.2]
    exact (hf _).2.2
theorem selectedProbeWordT8H (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) : ∃ w : List Nat,
      FiniteCoverWords.OverChoices w (probeChoices .t8h) ∧
      w.Pairwise (fun a b => idCompatible .t8h a b = true) ∧
      ∀ a ∈ w, ClusterRootOwned f ((candidateList .t8h).getD a fallback) := by
  classical
  let chosen : Nat → Nat := fun j => if hj : j < 15 then
    Classical.choose (probeSelectionsT8H f hf hr j hj) else 0
  have hchosen (j : Nat) (hj : j < 15) :
      chosen j ∈ (probeChoices .t8h).getD j [] ∧
      chosen j < (candidateList .t8h).length ∧
      (candidateList .t8h).getD (chosen j) fallback =
        f ((probeCells .t8h).getD j ⟨(0,0),0⟩) := by
    dsimp only [chosen]
    rw [dif_pos hj]
    exact Classical.choose_spec (probeSelectionsT8H f hf hr j hj)
  have hcompatible (i : Nat) (hi : i < 15) (j : Nat) (hj : j < 15) :
      (candidateList .t8h).getD (chosen i) fallback = (candidateList .t8h).getD (chosen j) fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList .t8h).getD (chosen i) fallback))
        (clusterPlacementCells ((candidateList .t8h).getD (chosen j) fallback)) := by
    rw [(hchosen i hi).2.2,(hchosen j hj).2.2]
    exact clusterField_compatible f hf _ _
  have hdomain := IndexedPruning.probePruneT8H_domain chosen
    (fun i hi => (hchosen i hi).1) hcompatible
  refine ⟨selectedIndexWord 15 chosen,
    selectedIndexWord_overChoices 15 chosen (probeChoices .t8h) (by rfl)
      (fun i hi => (hchosen i hi).1),?_,?_⟩
  · exact selectedIndexWord_pairwise .t8h 15 chosen (fun i hi j hj =>
      reducedCompatibilityT8H_sound (chosen i) (chosen j)
        (hdomain i hi) (hdomain j hj) (hcompatible i hi j hj))
  · apply selectedIndexWord_owned f .t8h 15 chosen
    intro i hi
    rw [(hchosen i hi).2.2]
    exact (hf _).2.2
theorem normalizedRawCaptures_checked : NormalizedRawCaptures := by
  apply normalizedRawCaptures_of_selected_words
  · intro f hf kind hk hr
    rcases hk with rfl | rfl
    · exact selectedProbeWordT7H f hf hr
    · exact selectedProbeWordT8H f hf hr
  · intro kind hk w hw
    rcases hk with rfl | rfl
    · apply probeSuffixT7H_covered w
      have he : FiniteCoverWords.enumerate (idCompatible .t7h) (probeChoices .t7h) = probeSuffixT7H6 := by
        simpa only [List.drop_zero] using probeSuffixT7H6_complete
      simpa only [he] using hw
    · apply probeSuffixT8H_covered w
      have he : FiniteCoverWords.enumerate (idCompatible .t8h) (probeChoices .t8h) = probeSuffixT8H15 := by
        simpa only [List.drop_zero] using probeSuffixT8H15_complete
      simpa only [he] using hw

theorem rawCaptures_checked : RawCaptures :=
  rawCaptures_of_normalized normalizedRawCaptures_checked
end SpectreClusters.StageD.Raw
