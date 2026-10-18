module

public import SpectreClusters.StageDRawProbePruneT8HRound0Cell6Data

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_6_part0 : [16,37,41,59,86,104,108,129,148,168,173,191].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 6 a (pruneWitnessesT8H0_6.getD a .keep)) = true := by rfl
end SpectreClusters.StageD.Raw.IndexedPruning
