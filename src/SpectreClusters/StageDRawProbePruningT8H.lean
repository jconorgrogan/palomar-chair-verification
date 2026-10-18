module

public import SpectreClusters.StageDRawReducedCompatibilityT8H
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell0
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell1
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell2
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell3
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell4
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell5
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell6
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell7
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell8
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell9
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell10
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell11
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell12
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell13
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell14
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell0
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell1
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell2
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell3
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell4
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell5
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell6
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell7
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell8
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell9
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell10
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell11
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell12
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell13
public import SpectreClusters.StageDRawProbePruneT8HRound1Cell14

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem probePruneT8H0_checked (i : Nat) (hi : i < pruneChoicesT8H0.length) :
    ∃ ws, probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 i ws = true := by
  have hin : i < 15 := hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pruneWitnessesT8H0_0,pruneWitnessesT8H0_0_checked⟩
  · exact ⟨pruneWitnessesT8H0_1,pruneWitnessesT8H0_1_checked⟩
  · exact ⟨pruneWitnessesT8H0_2,pruneWitnessesT8H0_2_checked⟩
  · exact ⟨pruneWitnessesT8H0_3,pruneWitnessesT8H0_3_checked⟩
  · exact ⟨pruneWitnessesT8H0_4,pruneWitnessesT8H0_4_checked⟩
  · exact ⟨pruneWitnessesT8H0_5,pruneWitnessesT8H0_5_checked⟩
  · exact ⟨pruneWitnessesT8H0_6,pruneWitnessesT8H0_6_checked⟩
  · exact ⟨pruneWitnessesT8H0_7,pruneWitnessesT8H0_7_checked⟩
  · exact ⟨pruneWitnessesT8H0_8,pruneWitnessesT8H0_8_checked⟩
  · exact ⟨pruneWitnessesT8H0_9,pruneWitnessesT8H0_9_checked⟩
  · exact ⟨pruneWitnessesT8H0_10,pruneWitnessesT8H0_10_checked⟩
  · exact ⟨pruneWitnessesT8H0_11,pruneWitnessesT8H0_11_checked⟩
  · exact ⟨pruneWitnessesT8H0_12,pruneWitnessesT8H0_12_checked⟩
  · exact ⟨pruneWitnessesT8H0_13,pruneWitnessesT8H0_13_checked⟩
  · exact ⟨pruneWitnessesT8H0_14,pruneWitnessesT8H0_14_checked⟩
theorem probePruneT8H1_checked (i : Nat) (hi : i < pruneChoicesT8H1.length) :
    ∃ ws, probePruneRowCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 i ws = true := by
  have hin : i < 15 := hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pruneWitnessesT8H1_0,pruneWitnessesT8H1_0_checked⟩
  · exact ⟨pruneWitnessesT8H1_1,pruneWitnessesT8H1_1_checked⟩
  · exact ⟨pruneWitnessesT8H1_2,pruneWitnessesT8H1_2_checked⟩
  · exact ⟨pruneWitnessesT8H1_3,pruneWitnessesT8H1_3_checked⟩
  · exact ⟨pruneWitnessesT8H1_4,pruneWitnessesT8H1_4_checked⟩
  · exact ⟨pruneWitnessesT8H1_5,pruneWitnessesT8H1_5_checked⟩
  · exact ⟨pruneWitnessesT8H1_6,pruneWitnessesT8H1_6_checked⟩
  · exact ⟨pruneWitnessesT8H1_7,pruneWitnessesT8H1_7_checked⟩
  · exact ⟨pruneWitnessesT8H1_8,pruneWitnessesT8H1_8_checked⟩
  · exact ⟨pruneWitnessesT8H1_9,pruneWitnessesT8H1_9_checked⟩
  · exact ⟨pruneWitnessesT8H1_10,pruneWitnessesT8H1_10_checked⟩
  · exact ⟨pruneWitnessesT8H1_11,pruneWitnessesT8H1_11_checked⟩
  · exact ⟨pruneWitnessesT8H1_12,pruneWitnessesT8H1_12_checked⟩
  · exact ⟨pruneWitnessesT8H1_13,pruneWitnessesT8H1_13_checked⟩
  · exact ⟨pruneWitnessesT8H1_14,pruneWitnessesT8H1_14_checked⟩
set_option maxRecDepth 100000 in
theorem probePruneT8H_domain_checked :
    pruneChoicesT8H2.all (fun cs => cs.all reducedDomainT8H.contains) = true := by rfl

theorem probePruneT8H_domain (chosen : Nat → Nat)
    (hchoices : ∀ i, i < 15 → chosen i ∈ (probeChoices .t8h).getD i [])
    (hcompatible : ∀ i, i < 15 → ∀ j, j < 15 →
      (candidateList .t8h).getD (chosen i) fallback = (candidateList .t8h).getD (chosen j) fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList .t8h).getD (chosen i) fallback))
        (clusterPlacementCells ((candidateList .t8h).getD (chosen j) fallback))) :
    ∀ i, i < 15 → chosen i ∈ reducedDomainT8H := by
  have h0 : ∀ i, i < pruneChoicesT8H0.length → chosen i ∈ pruneChoicesT8H0.getD i [] := by
    intro i hi
    have hin : i < 15 := hi
    simpa only [pruneChoicesT8H_initial] using hchoices i hin
  have h1 := probePruneAll_sound .t8h pruneChoicesT8H0 pruneChoicesT8H1 chosen probePruneT8H0_checked h0 hcompatible
  have h2 := probePruneAll_sound .t8h pruneChoicesT8H1 pruneChoicesT8H2 chosen probePruneT8H1_checked h1 hcompatible
  intro i hi
  have hil : i < pruneChoicesT8H2.length := hi
  have hm : pruneChoicesT8H2.getD i [] ∈ pruneChoicesT8H2 := by
    simpa [List.getD_eq_getElem?_getD,hil] using (List.getElem_mem hil)
  have hall := List.all_eq_true.mp probePruneT8H_domain_checked _ hm
  have hc := List.all_eq_true.mp hall (chosen i) (h2 i hi)
  simpa only [List.contains_iff_mem] using hc
end SpectreClusters.StageD.Raw.IndexedPruning
