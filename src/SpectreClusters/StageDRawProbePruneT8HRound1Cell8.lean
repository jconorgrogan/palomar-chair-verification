module

public import SpectreClusters.StageDRawProbePruneT8HData

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
def pruneWitnessesT8H1_8 : List ProbePruneWitness := [.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep]
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H1_8_piece0 : [30,37,104,162].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 8 a (pruneWitnessesT8H1_8.getD a .keep)) = true := by rfl
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H1_8_piece1 : [168,191,236,251].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 8 a (pruneWitnessesT8H1_8.getD a .keep)) = true := by rfl
theorem pruneWitnessesT8H1_8_checked : probePruneRowCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 8 pruneWitnessesT8H1_8 = true := by
  change ([30,37,104,162] ++ [168,191,236,251]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 8 a (pruneWitnessesT8H1_8.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H1_8_piece0,pruneWitnessesT8H1_8_piece1,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
