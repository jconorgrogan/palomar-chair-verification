module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell13Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_13_part1 : [71,91,94,96,115,118,134].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 13 a (pruneWitnessesT8H0_13.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
