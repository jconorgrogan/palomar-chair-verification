module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell35Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H10_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 10 []) witnessesT8H35 = true := by rfl
end SpectreClusters.StageD.Raw
