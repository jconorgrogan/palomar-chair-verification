module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT7HCell38Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT7H4_checked : witnessChoicesCheck
    ((probeChoices .t7h).getD 4 []) witnessesT7H38 = true := by rfl
end SpectreClusters.StageD.Raw
