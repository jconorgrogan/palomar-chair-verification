module

public import SpectreClusters.StageDRawProbePruneT8HData

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
def pruneWitnessesT8H0_1 : List ProbePruneWitness := [.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep]
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_1_piece0 : [12,55,77,100].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 1 a (pruneWitnessesT8H0_1.getD a .keep)) = true := by rfl
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_1_piece1 : [123,144,165,187].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 1 a (pruneWitnessesT8H0_1.getD a .keep)) = true := by rfl
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H0_1_piece2 : [209,232,256].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 1 a (pruneWitnessesT8H0_1.getD a .keep)) = true := by rfl
theorem pruneWitnessesT8H0_1_checked : probePruneRowCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 1 pruneWitnessesT8H0_1 = true := by
  change ([12,55,77,100] ++ [123,144,165,187] ++ [209,232,256]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H0 pruneChoicesT8H1 1 a (pruneWitnessesT8H0_1.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H0_1_piece0,pruneWitnessesT8H0_1_piece1,pruneWitnessesT8H0_1_piece2,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
