module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell8Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H1_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 1 []) witnessesT8H8 = true := by rfl
end SpectreClusters.StageD.Raw
