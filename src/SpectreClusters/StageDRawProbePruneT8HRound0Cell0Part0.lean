module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell0Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_0_part0 : [15,35,36,39,55,58].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 0 a (pruneWitnessesT8H0_0.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
