module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell7Part0
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell7Part1
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell7Part2
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell7Part3

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem pruneWitnessesT8H0_7_checked : probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 7 pruneWitnessesT8H0_7 = true := by
  change ([11,14,16,32,37,57,76,79] ++ [81,102,104,120,125,143] ++ [146,148,164,168,189,191,208,213,231] ++ [234,236,253,258]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 7 a (pruneWitnessesT8H0_7.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H0_7_part0,pruneWitnessesT8H0_7_part1,pruneWitnessesT8H0_7_part2,pruneWitnessesT8H0_7_part3,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
