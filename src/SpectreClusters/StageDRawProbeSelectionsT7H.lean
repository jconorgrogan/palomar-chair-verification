module

public import SpectreClusters.StageDRawProbeSemantics
public import SpectreClusters.StageDRawProbeCandidateT7HCell4
public import SpectreClusters.StageDRawProbeCandidateT7HCell11
public import SpectreClusters.StageDRawProbeCandidateT7HCell20
public import SpectreClusters.StageDRawProbeCandidateT7HCell31
public import SpectreClusters.StageDRawProbeCandidateT7HCell38
public import SpectreClusters.StageDRawProbeCandidateT7HCell50
public import SpectreClusters.StageDRawProbeChoiceWitnessT7HCell0
public import SpectreClusters.StageDRawProbeChoiceWitnessT7HCell1
public import SpectreClusters.StageDRawProbeChoiceWitnessT7HCell2
public import SpectreClusters.StageDRawProbeChoiceWitnessT7HCell3
public import SpectreClusters.StageDRawProbeChoiceWitnessT7HCell4
public import SpectreClusters.StageDRawProbeChoiceWitnessT7HCell5

@[expose] public section

namespace SpectreClusters.StageD.Raw
theorem probeSelectionT7H0 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t7h)) :
    ∃ a, a ∈ ((probeChoices .t7h).getD 0 []) ∧ a < (candidateList .t7h).length ∧
      (candidateList .t7h).getD a fallback = f ((probeCells .t7h).getD 0 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t7h) (candidateList .t7h) ((probeCells .t7h).getD 0 ⟨(0,0),0⟩)
    witnessesT7H4 ((probeChoices .t7h).getD 0 []) (by rfl) probeAlignedT7H4_checked
    probeChoiceWitnessT7H0_checked (f ((probeCells .t7h).getD 0 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t7h]
  exact probe_owner_disjoint f hf .t7h hr ((probeCells .t7h).getD 0 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT7H1 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t7h)) :
    ∃ a, a ∈ ((probeChoices .t7h).getD 1 []) ∧ a < (candidateList .t7h).length ∧
      (candidateList .t7h).getD a fallback = f ((probeCells .t7h).getD 1 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t7h) (candidateList .t7h) ((probeCells .t7h).getD 1 ⟨(0,0),0⟩)
    witnessesT7H11 ((probeChoices .t7h).getD 1 []) (by rfl) probeAlignedT7H11_checked
    probeChoiceWitnessT7H1_checked (f ((probeCells .t7h).getD 1 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t7h]
  exact probe_owner_disjoint f hf .t7h hr ((probeCells .t7h).getD 1 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT7H2 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t7h)) :
    ∃ a, a ∈ ((probeChoices .t7h).getD 2 []) ∧ a < (candidateList .t7h).length ∧
      (candidateList .t7h).getD a fallback = f ((probeCells .t7h).getD 2 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t7h) (candidateList .t7h) ((probeCells .t7h).getD 2 ⟨(0,0),0⟩)
    witnessesT7H20 ((probeChoices .t7h).getD 2 []) (by rfl) probeAlignedT7H20_checked
    probeChoiceWitnessT7H2_checked (f ((probeCells .t7h).getD 2 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t7h]
  exact probe_owner_disjoint f hf .t7h hr ((probeCells .t7h).getD 2 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT7H3 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t7h)) :
    ∃ a, a ∈ ((probeChoices .t7h).getD 3 []) ∧ a < (candidateList .t7h).length ∧
      (candidateList .t7h).getD a fallback = f ((probeCells .t7h).getD 3 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t7h) (candidateList .t7h) ((probeCells .t7h).getD 3 ⟨(0,0),0⟩)
    witnessesT7H31 ((probeChoices .t7h).getD 3 []) (by rfl) probeAlignedT7H31_checked
    probeChoiceWitnessT7H3_checked (f ((probeCells .t7h).getD 3 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t7h]
  exact probe_owner_disjoint f hf .t7h hr ((probeCells .t7h).getD 3 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT7H4 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t7h)) :
    ∃ a, a ∈ ((probeChoices .t7h).getD 4 []) ∧ a < (candidateList .t7h).length ∧
      (candidateList .t7h).getD a fallback = f ((probeCells .t7h).getD 4 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t7h) (candidateList .t7h) ((probeCells .t7h).getD 4 ⟨(0,0),0⟩)
    witnessesT7H38 ((probeChoices .t7h).getD 4 []) (by rfl) probeAlignedT7H38_checked
    probeChoiceWitnessT7H4_checked (f ((probeCells .t7h).getD 4 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t7h]
  exact probe_owner_disjoint f hf .t7h hr ((probeCells .t7h).getD 4 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT7H5 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t7h)) :
    ∃ a, a ∈ ((probeChoices .t7h).getD 5 []) ∧ a < (candidateList .t7h).length ∧
      (candidateList .t7h).getD a fallback = f ((probeCells .t7h).getD 5 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t7h) (candidateList .t7h) ((probeCells .t7h).getD 5 ⟨(0,0),0⟩)
    witnessesT7H50 ((probeChoices .t7h).getD 5 []) (by rfl) probeAlignedT7H50_checked
    probeChoiceWitnessT7H5_checked (f ((probeCells .t7h).getD 5 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t7h]
  exact probe_owner_disjoint f hf .t7h hr ((probeCells .t7h).getD 5 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionsT7H (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t7h)) (j : Nat) (hj : j < 6) :
    ∃ a, a ∈ (probeChoices .t7h).getD j [] ∧ a < (candidateList .t7h).length ∧
      (candidateList .t7h).getD a fallback = f ((probeCells .t7h).getD j ⟨(0,0),0⟩) := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact probeSelectionT7H0 f hf hr
  · exact probeSelectionT7H1 f hf hr
  · exact probeSelectionT7H2 f hf hr
  · exact probeSelectionT7H3 f hf hr
  · exact probeSelectionT7H4 f hf hr
  · exact probeSelectionT7H5 f hf hr
end SpectreClusters.StageD.Raw
