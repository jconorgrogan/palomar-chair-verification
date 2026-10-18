module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell3Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_3_part1 : [171,187,193,216,217,238,256,260,261].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 3 a (pruneWitnessesT8H0_3.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
