module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell31Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H9_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 9 []) witnessesT8H31 = true := by rfl
end SpectreClusters.StageD.Raw
