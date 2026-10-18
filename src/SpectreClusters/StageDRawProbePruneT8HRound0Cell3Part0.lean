module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell3Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_3_part0 : [35,39,55,84,106,123,127,128,144].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 3 a (pruneWitnessesT8H0_3.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
