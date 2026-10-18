module

public import SpectreClusters.StageDRawProbeSemantics
public import SpectreClusters.StageDRawProbeCandidateT8HCell7
public import SpectreClusters.StageDRawProbeCandidateT8HCell8
public import SpectreClusters.StageDRawProbeCandidateT8HCell9
public import SpectreClusters.StageDRawProbeCandidateT8HCell10
public import SpectreClusters.StageDRawProbeCandidateT8HCell17
public import SpectreClusters.StageDRawProbeCandidateT8HCell21
public import SpectreClusters.StageDRawProbeCandidateT8HCell25
public import SpectreClusters.StageDRawProbeCandidateT8HCell26
public import SpectreClusters.StageDRawProbeCandidateT8HCell28
public import SpectreClusters.StageDRawProbeCandidateT8HCell31
public import SpectreClusters.StageDRawProbeCandidateT8HCell35
public import SpectreClusters.StageDRawProbeCandidateT8HCell41
public import SpectreClusters.StageDRawProbeCandidateT8HCell42
public import SpectreClusters.StageDRawProbeCandidateT8HCell44
public import SpectreClusters.StageDRawProbeCandidateT8HCell51
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell0
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell1
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell2
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell3
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell4
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell5
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell6
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell7
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell8
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell9
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell10
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell11
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell12
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell13
public import SpectreClusters.StageDRawProbeChoiceWitnessT8HCell14

@[expose] public section

namespace SpectreClusters.StageD.Raw
theorem probeSelectionT8H0 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 0 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 0 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 0 ⟨(0,0),0⟩)
    witnessesT8H7 ((probeChoices .t8h).getD 0 []) (by rfl) probeAlignedT8H7_checked
    probeChoiceWitnessT8H0_checked (f ((probeCells .t8h).getD 0 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 0 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H1 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 1 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 1 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 1 ⟨(0,0),0⟩)
    witnessesT8H8 ((probeChoices .t8h).getD 1 []) (by rfl) probeAlignedT8H8_checked
    probeChoiceWitnessT8H1_checked (f ((probeCells .t8h).getD 1 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 1 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H2 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 2 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 2 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 2 ⟨(0,0),0⟩)
    witnessesT8H9 ((probeChoices .t8h).getD 2 []) (by rfl) probeAlignedT8H9_checked
    probeChoiceWitnessT8H2_checked (f ((probeCells .t8h).getD 2 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 2 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H3 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 3 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 3 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 3 ⟨(0,0),0⟩)
    witnessesT8H10 ((probeChoices .t8h).getD 3 []) (by rfl) probeAlignedT8H10_checked
    probeChoiceWitnessT8H3_checked (f ((probeCells .t8h).getD 3 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 3 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H4 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 4 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 4 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 4 ⟨(0,0),0⟩)
    witnessesT8H17 ((probeChoices .t8h).getD 4 []) (by rfl) probeAlignedT8H17_checked
    probeChoiceWitnessT8H4_checked (f ((probeCells .t8h).getD 4 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 4 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H5 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 5 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 5 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 5 ⟨(0,0),0⟩)
    witnessesT8H21 ((probeChoices .t8h).getD 5 []) (by rfl) probeAlignedT8H21_checked
    probeChoiceWitnessT8H5_checked (f ((probeCells .t8h).getD 5 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 5 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H6 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 6 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 6 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 6 ⟨(0,0),0⟩)
    witnessesT8H25 ((probeChoices .t8h).getD 6 []) (by rfl) probeAlignedT8H25_checked
    probeChoiceWitnessT8H6_checked (f ((probeCells .t8h).getD 6 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 6 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H7 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 7 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 7 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 7 ⟨(0,0),0⟩)
    witnessesT8H26 ((probeChoices .t8h).getD 7 []) (by rfl) probeAlignedT8H26_checked
    probeChoiceWitnessT8H7_checked (f ((probeCells .t8h).getD 7 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 7 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H8 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 8 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 8 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 8 ⟨(0,0),0⟩)
    witnessesT8H28 ((probeChoices .t8h).getD 8 []) (by rfl) probeAlignedT8H28_checked
    probeChoiceWitnessT8H8_checked (f ((probeCells .t8h).getD 8 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 8 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H9 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 9 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 9 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 9 ⟨(0,0),0⟩)
    witnessesT8H31 ((probeChoices .t8h).getD 9 []) (by rfl) probeAlignedT8H31_checked
    probeChoiceWitnessT8H9_checked (f ((probeCells .t8h).getD 9 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 9 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H10 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 10 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 10 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 10 ⟨(0,0),0⟩)
    witnessesT8H35 ((probeChoices .t8h).getD 10 []) (by rfl) probeAlignedT8H35_checked
    probeChoiceWitnessT8H10_checked (f ((probeCells .t8h).getD 10 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 10 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H11 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 11 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 11 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 11 ⟨(0,0),0⟩)
    witnessesT8H41 ((probeChoices .t8h).getD 11 []) (by rfl) probeAlignedT8H41_checked
    probeChoiceWitnessT8H11_checked (f ((probeCells .t8h).getD 11 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 11 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H12 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 12 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 12 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 12 ⟨(0,0),0⟩)
    witnessesT8H42 ((probeChoices .t8h).getD 12 []) (by rfl) probeAlignedT8H42_checked
    probeChoiceWitnessT8H12_checked (f ((probeCells .t8h).getD 12 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 12 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H13 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 13 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 13 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 13 ⟨(0,0),0⟩)
    witnessesT8H44 ((probeChoices .t8h).getD 13 []) (by rfl) probeAlignedT8H44_checked
    probeChoiceWitnessT8H13_checked (f ((probeCells .t8h).getD 13 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 13 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionT8H14 (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) :
    ∃ a, a ∈ ((probeChoices .t8h).getD 14 []) ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD 14 ⟨(0,0),0⟩) := by
  apply alignedChecks_choice (clusterCells .t8h) (candidateList .t8h) ((probeCells .t8h).getD 14 ⟨(0,0),0⟩)
    witnessesT8H51 ((probeChoices .t8h).getD 14 []) (by rfl) probeAlignedT8H51_checked
    probeChoiceWitnessT8H14_checked (f ((probeCells .t8h).getD 14 ⟨(0,0),0⟩))
    (mem_alignedAt _ _ (hf _).1 (hf _).2.1)
  rw [←canonical_cluster_cells .t8h]
  exact probe_owner_disjoint f hf .t8h hr ((probeCells .t8h).getD 14 ⟨(0,0),0⟩) (by decide)
theorem probeSelectionsT8H (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hr : ClusterRootOwned f (canonical .t8h)) (j : Nat) (hj : j < 15) :
    ∃ a, a ∈ (probeChoices .t8h).getD j [] ∧ a < (candidateList .t8h).length ∧
      (candidateList .t8h).getD a fallback = f ((probeCells .t8h).getD j ⟨(0,0),0⟩) := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact probeSelectionT8H0 f hf hr
  · exact probeSelectionT8H1 f hf hr
  · exact probeSelectionT8H2 f hf hr
  · exact probeSelectionT8H3 f hf hr
  · exact probeSelectionT8H4 f hf hr
  · exact probeSelectionT8H5 f hf hr
  · exact probeSelectionT8H6 f hf hr
  · exact probeSelectionT8H7 f hf hr
  · exact probeSelectionT8H8 f hf hr
  · exact probeSelectionT8H9 f hf hr
  · exact probeSelectionT8H10 f hf hr
  · exact probeSelectionT8H11 f hf hr
  · exact probeSelectionT8H12 f hf hr
  · exact probeSelectionT8H13 f hf hr
  · exact probeSelectionT8H14 f hf hr
end SpectreClusters.StageD.Raw
