module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell17Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H4_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 4 []) witnessesT8H17 = true := by rfl
end SpectreClusters.StageD.Raw
