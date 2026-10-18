module

public import SpectreClusters.StageDRawReducedCompatibilityT7H
public import SpectreClusters.StageDRawProbePruneT7HRound0Cell0
public import SpectreClusters.StageDRawProbePruneT7HRound0Cell1
public import SpectreClusters.StageDRawProbePruneT7HRound0Cell2
public import SpectreClusters.StageDRawProbePruneT7HRound0Cell3
public import SpectreClusters.StageDRawProbePruneT7HRound0Cell4
public import SpectreClusters.StageDRawProbePruneT7HRound0Cell5
public import SpectreClusters.StageDRawProbePruneT7HRound1Cell0
public import SpectreClusters.StageDRawProbePruneT7HRound1Cell1
public import SpectreClusters.StageDRawProbePruneT7HRound1Cell2
public import SpectreClusters.StageDRawProbePruneT7HRound1Cell3
public import SpectreClusters.StageDRawProbePruneT7HRound1Cell4
public import SpectreClusters.StageDRawProbePruneT7HRound1Cell5
public import SpectreClusters.StageDRawProbePruneT7HRound2Cell0
public import SpectreClusters.StageDRawProbePruneT7HRound2Cell1
public import SpectreClusters.StageDRawProbePruneT7HRound2Cell2
public import SpectreClusters.StageDRawProbePruneT7HRound2Cell3
public import SpectreClusters.StageDRawProbePruneT7HRound2Cell4
public import SpectreClusters.StageDRawProbePruneT7HRound2Cell5
public import SpectreClusters.StageDRawProbePruneT7HRound3Cell0
public import SpectreClusters.StageDRawProbePruneT7HRound3Cell1
public import SpectreClusters.StageDRawProbePruneT7HRound3Cell2
public import SpectreClusters.StageDRawProbePruneT7HRound3Cell3
public import SpectreClusters.StageDRawProbePruneT7HRound3Cell4
public import SpectreClusters.StageDRawProbePruneT7HRound3Cell5

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem probePruneT7H0_checked (i : Nat) (hi : i < pruneChoicesT7H0.length) :
    ∃ ws, probePruneRowCheck .t7h pruneChoicesT7H0 pruneChoicesT7H1 i ws = true := by
  have hin : i < 6 := hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pruneWitnessesT7H0_0,pruneWitnessesT7H0_0_checked⟩
  · exact ⟨pruneWitnessesT7H0_1,pruneWitnessesT7H0_1_checked⟩
  · exact ⟨pruneWitnessesT7H0_2,pruneWitnessesT7H0_2_checked⟩
  · exact ⟨pruneWitnessesT7H0_3,pruneWitnessesT7H0_3_checked⟩
  · exact ⟨pruneWitnessesT7H0_4,pruneWitnessesT7H0_4_checked⟩
  · exact ⟨pruneWitnessesT7H0_5,pruneWitnessesT7H0_5_checked⟩
theorem probePruneT7H1_checked (i : Nat) (hi : i < pruneChoicesT7H1.length) :
    ∃ ws, probePruneRowCheck .t7h pruneChoicesT7H1 pruneChoicesT7H2 i ws = true := by
  have hin : i < 6 := hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pruneWitnessesT7H1_0,pruneWitnessesT7H1_0_checked⟩
  · exact ⟨pruneWitnessesT7H1_1,pruneWitnessesT7H1_1_checked⟩
  · exact ⟨pruneWitnessesT7H1_2,pruneWitnessesT7H1_2_checked⟩
  · exact ⟨pruneWitnessesT7H1_3,pruneWitnessesT7H1_3_checked⟩
  · exact ⟨pruneWitnessesT7H1_4,pruneWitnessesT7H1_4_checked⟩
  · exact ⟨pruneWitnessesT7H1_5,pruneWitnessesT7H1_5_checked⟩
theorem probePruneT7H2_checked (i : Nat) (hi : i < pruneChoicesT7H2.length) :
    ∃ ws, probePruneRowCheck .t7h pruneChoicesT7H2 pruneChoicesT7H3 i ws = true := by
  have hin : i < 6 := hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pruneWitnessesT7H2_0,pruneWitnessesT7H2_0_checked⟩
  · exact ⟨pruneWitnessesT7H2_1,pruneWitnessesT7H2_1_checked⟩
  · exact ⟨pruneWitnessesT7H2_2,pruneWitnessesT7H2_2_checked⟩
  · exact ⟨pruneWitnessesT7H2_3,pruneWitnessesT7H2_3_checked⟩
  · exact ⟨pruneWitnessesT7H2_4,pruneWitnessesT7H2_4_checked⟩
  · exact ⟨pruneWitnessesT7H2_5,pruneWitnessesT7H2_5_checked⟩
theorem probePruneT7H3_checked (i : Nat) (hi : i < pruneChoicesT7H3.length) :
    ∃ ws, probePruneRowCheck .t7h pruneChoicesT7H3 pruneChoicesT7H4 i ws = true := by
  have hin : i < 6 := hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pruneWitnessesT7H3_0,pruneWitnessesT7H3_0_checked⟩
  · exact ⟨pruneWitnessesT7H3_1,pruneWitnessesT7H3_1_checked⟩
  · exact ⟨pruneWitnessesT7H3_2,pruneWitnessesT7H3_2_checked⟩
  · exact ⟨pruneWitnessesT7H3_3,pruneWitnessesT7H3_3_checked⟩
  · exact ⟨pruneWitnessesT7H3_4,pruneWitnessesT7H3_4_checked⟩
  · exact ⟨pruneWitnessesT7H3_5,pruneWitnessesT7H3_5_checked⟩
set_option maxRecDepth 100000 in
theorem probePruneT7H_domain_checked :
    pruneChoicesT7H4.all (fun cs => cs.all reducedDomainT7H.contains) = true := by rfl

theorem probePruneT7H_domain (chosen : Nat → Nat)
    (hchoices : ∀ i, i < 6 → chosen i ∈ (probeChoices .t7h).getD i [])
    (hcompatible : ∀ i, i < 6 → ∀ j, j < 6 →
      (candidateList .t7h).getD (chosen i) fallback = (candidateList .t7h).getD (chosen j) fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList .t7h).getD (chosen i) fallback))
        (clusterPlacementCells ((candidateList .t7h).getD (chosen j) fallback))) :
    ∀ i, i < 6 → chosen i ∈ reducedDomainT7H := by
  have h0 : ∀ i, i < pruneChoicesT7H0.length → chosen i ∈ pruneChoicesT7H0.getD i [] := by
    intro i hi
    have hin : i < 6 := hi
    simpa only [pruneChoicesT7H_initial] using hchoices i hin
  have h1 := probePruneAll_sound .t7h pruneChoicesT7H0 pruneChoicesT7H1 chosen probePruneT7H0_checked h0 hcompatible
  have h2 := probePruneAll_sound .t7h pruneChoicesT7H1 pruneChoicesT7H2 chosen probePruneT7H1_checked h1 hcompatible
  have h3 := probePruneAll_sound .t7h pruneChoicesT7H2 pruneChoicesT7H3 chosen probePruneT7H2_checked h2 hcompatible
  have h4 := probePruneAll_sound .t7h pruneChoicesT7H3 pruneChoicesT7H4 chosen probePruneT7H3_checked h3 hcompatible
  intro i hi
  have hil : i < pruneChoicesT7H4.length := hi
  have hm : pruneChoicesT7H4.getD i [] ∈ pruneChoicesT7H4 := by
    simpa [List.getD_eq_getElem?_getD,hil] using (List.getElem_mem hil)
  have hall := List.all_eq_true.mp probePruneT7H_domain_checked _ hm
  have hc := List.all_eq_true.mp hall (chosen i) (h4 i hi)
  simpa only [List.contains_iff_mem] using hc
end SpectreClusters.StageD.Raw.IndexedPruning
