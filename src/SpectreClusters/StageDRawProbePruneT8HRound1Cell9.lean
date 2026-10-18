module

public import SpectreClusters.StageDRawProbePruneT8HData

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
def pruneWitnessesT8H1_9 : List ProbePruneWitness := [.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep]
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H1_9_piece0 : [28,48,95,116].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 9 a (pruneWitnessesT8H1_9.getD a .keep)) = true := by rfl
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H1_9_piece1 : [137,180,228,249].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 9 a (pruneWitnessesT8H1_9.getD a .keep)) = true := by rfl
theorem pruneWitnessesT8H1_9_checked : probePruneRowCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 9 pruneWitnessesT8H1_9 = true := by
  change ([28,48,95,116] ++ [137,180,228,249]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 9 a (pruneWitnessesT8H1_9.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H1_9_piece0,pruneWitnessesT8H1_9_piece1,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
