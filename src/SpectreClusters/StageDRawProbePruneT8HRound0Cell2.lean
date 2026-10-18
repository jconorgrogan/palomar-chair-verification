module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell2Part0
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell2Part1
public import SpectreClusters.StageDRawProbePruneT8HRound0Cell2Part2

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
theorem pruneWitnessesT8H0_2_checked : probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 2 pruneWitnessesT8H0_2 = true := by
  change ([7,8,12,28,29,49,55,72] ++ [73,77,95,100,117,139,144,160,161,165] ++ [181,187,204,205,209,228,232,249,250]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 2 a (pruneWitnessesT8H0_2.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H0_2_part0,pruneWitnessesT8H0_2_part1,pruneWitnessesT8H0_2_part2,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
