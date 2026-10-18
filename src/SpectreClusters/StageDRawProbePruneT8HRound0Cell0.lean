module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell0Part0
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell0Part1
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell0Part2
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell0Part3

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem pruneWitnessesT8H0_0_checked : probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 0 pruneWitnessesT8H0_0 = true := by
  change ([15,35,36,39,55,58] ++ [80,84,100,103,106,123,127,144,147] ++ [167,171,187,190,193,212] ++ [216,232,235,238,256,260]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 0 a (pruneWitnessesT8H0_0.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H0_0_part0,pruneWitnessesT8H0_0_part1,pruneWitnessesT8H0_0_part2,pruneWitnessesT8H0_0_part3,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
