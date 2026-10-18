module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell10Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H3_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 3 []) witnessesT8H10 = true := by rfl
end SpectreClusters.StageD.Raw
