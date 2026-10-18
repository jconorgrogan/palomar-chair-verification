module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell11Part0
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell11Part1
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell11Part2
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell11Part3
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell11Part4
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell11Part5

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem pruneWitnessesT8H0_11_checked : probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 11 pruneWitnessesT8H0_11 = true := by
  change ([2,3,4,24,25,45,46] ++ [47,50,68,69,91] ++ [92,96,112,114,118,133,134,135] ++ [136,156,157,177,178,179,182] ++ [200,201,206,223,224,225] ++ [245,246,251]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 11 a (pruneWitnessesT8H0_11.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H0_11_part0,pruneWitnessesT8H0_11_part1,pruneWitnessesT8H0_11_part2,pruneWitnessesT8H0_11_part3,pruneWitnessesT8H0_11_part4,pruneWitnessesT8H0_11_part5,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
