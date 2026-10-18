module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell6Part0
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell6Part1

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem pruneWitnessesT8H0_6_checked : probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 6 pruneWitnessesT8H0_6 = true := by
  change ([16,37,41,59,86,104,108,129,148,168,173,191] ++ [195,218,236,240,262]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 6 a (pruneWitnessesT8H0_6.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H0_6_part0,pruneWitnessesT8H0_6_part1,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
