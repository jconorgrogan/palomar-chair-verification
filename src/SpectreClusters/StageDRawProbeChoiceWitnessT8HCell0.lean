module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell7Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H0_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 0 []) witnessesT8H7 = true := by rfl
end SpectreClusters.StageD.Raw
