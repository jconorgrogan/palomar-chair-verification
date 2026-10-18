module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT7HCell50Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT7H5_checked : witnessChoicesCheck
    ((probeChoices .t7h).getD 5 []) witnessesT7H50 = true := by rfl
end SpectreClusters.StageD.Raw
