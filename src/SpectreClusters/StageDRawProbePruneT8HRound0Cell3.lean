module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell3Part0
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell3Part1

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem pruneWitnessesT8H0_3_checked : probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 3 pruneWitnessesT8H0_3 = true := by
  change ([35,39,55,84,106,123,127,128,144] ++ [171,187,193,216,217,238,256,260,261]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 3 a (pruneWitnessesT8H0_3.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H0_3_part0,pruneWitnessesT8H0_3_part1,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
