module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell51Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H14_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 14 []) witnessesT8H51 = true := by rfl
end SpectreClusters.StageD.Raw
