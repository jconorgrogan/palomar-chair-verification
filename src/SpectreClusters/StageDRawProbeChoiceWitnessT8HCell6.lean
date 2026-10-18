module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell25Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H6_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 6 []) witnessesT8H25 = true := by rfl
end SpectreClusters.StageD.Raw
