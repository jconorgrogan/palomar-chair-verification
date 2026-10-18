module

public import SpectreClusters.StageDRawProbePruneT8HData

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
def pruneWitnessesT8H1_10 : List ProbePruneWitness := [.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep,.keep]
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H1_10_piece0 : [28,48,114,116].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 10 a (pruneWitnessesT8H1_10.getD a .keep)) = true := by rfl
set_option maxRecDepth 100000 in
theorem pruneWitnessesT8H1_10_piece1 : [137,180,249].all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 10 a (pruneWitnessesT8H1_10.getD a .keep)) = true := by rfl
theorem pruneWitnessesT8H1_10_checked : probePruneRowCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 10 pruneWitnessesT8H1_10 = true := by
  change ([28,48,114,116] ++ [137,180,249]).all
    (fun a => probePruneEntryCheck .t8h pruneChoicesT8H1 pruneChoicesT8H2 10 a (pruneWitnessesT8H1_10.getD a .keep)) = true
  simp only [List.all_append,pruneWitnessesT8H1_10_piece0,pruneWitnessesT8H1_10_piece1,Bool.and_self]
end SpectreClusters.StageD.Raw.IndexedPruning
