module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT7HCell4Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT7H0_checked : witnessChoicesCheck
    ((probeChoices .t7h).getD 0 []) witnessesT7H4 = true := by rfl
end SpectreClusters.StageD.Raw
