module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell2Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_2_part2 : [181,187,204,205,209,228,232,249,250].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 2 a (pruneWitnessesT8H0_2.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
