module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell8Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_8_part1 : [164,168,191,208,231,236,251,253].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 8 a (pruneWitnessesT8H0_8.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
