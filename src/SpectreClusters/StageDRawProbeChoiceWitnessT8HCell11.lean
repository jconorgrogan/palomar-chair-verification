module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell41Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H11_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 11 []) witnessesT8H41 = true := by rfl
end SpectreClusters.StageD.Raw
