module

public import SpectreClusters.StageDRawProbePruneT8HData

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
def pruneWitnessesT8H1_3 : List ProbePruneWitness := [.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep]
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H1_3_piece0 : [55,123,144,187].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 3 a (pruneWitnessesT8H1_3.getD a .keep)) = true := by rfl
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H1_3_piece1 : [217,256].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 3 a (pruneWitnessesT8H1_3.getD a .keep)) = true := by rfl
theorem pruneWitnessesT8H1_3_checked : probePruneRowCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 3 pruneWitnessesT8H1_3 = true := by
  change ([55,123,144,187] ++ [217,256]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 3 a (pruneWitnessesT8H1_3.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H1_3_piece0,pruneWitnessesT8H1_3_piece1,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
