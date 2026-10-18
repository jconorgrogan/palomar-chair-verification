module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell8Part0
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell8Part1

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem pruneWitnessesT8H0_8_checked : probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 8 pruneWitnessesT8H0_8 = true := by
  change ([11,30,32,37,76,81,104,120,143,162] ++ [164,168,191,208,231,236,251,253]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 8 a (pruneWitnessesT8H0_8.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H0_8_part0,pruneWitnessesT8H0_8_part1,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
