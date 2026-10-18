module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell2Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_2_part0 : [7,8,12,28,29,49,55,72].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 2 a (pruneWitnessesT8H0_2.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
