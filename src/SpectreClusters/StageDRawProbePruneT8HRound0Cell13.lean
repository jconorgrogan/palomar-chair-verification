module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell13Part0
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell13Part1
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell13Part2
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell13Part3

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem pruneWitnessesT8H0_13_checked : probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 13 pruneWitnessesT8H0_13 = true := by
  change ([2,6,24,27,30,46,50] ++ [71,91,94,96,115,118,134] ++ [138,156,159,162,178,182,203,206] ++ [223,227,245,248,251]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 13 a (pruneWitnessesT8H0_13.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H0_13_part0,pruneWitnessesT8H0_13_part1,pruneWitnessesT8H0_13_part2,pruneWitnessesT8H0_13_part3,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
