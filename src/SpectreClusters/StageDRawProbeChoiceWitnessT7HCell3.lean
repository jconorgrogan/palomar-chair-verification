module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT7HCell31Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT7H3_checked : witnessChoicesCheck
    ((probeChoices .t7h).getD 3 []) witnessesT7H31 = true := by rfl
end SpectreClusters.StageD.Raw
