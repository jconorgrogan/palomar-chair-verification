module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT7HCell11Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT7H1_checked : witnessChoicesCheck
    ((probeChoices .t7h).getD 1 []) witnessesT7H11 = true := by rfl
end SpectreClusters.StageD.Raw
