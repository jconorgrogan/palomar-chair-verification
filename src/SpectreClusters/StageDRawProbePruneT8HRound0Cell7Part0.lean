module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell7Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_7_part0 : [11,14,16,32,37,57,76,79].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 7 a (pruneWitnessesT8H0_7.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
