module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell11Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_11_part2 : [92,96,112,114,118,133,134,135].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 11 a (pruneWitnessesT8H0_11.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
