module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT7HCell20Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT7H2_checked : witnessChoicesCheck
    ((probeChoices .t7h).getD 2 []) witnessesT7H20 = true := by rfl
end SpectreClusters.StageD.Raw
