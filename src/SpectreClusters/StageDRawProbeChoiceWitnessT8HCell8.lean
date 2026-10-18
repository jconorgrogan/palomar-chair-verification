module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell28Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H8_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 8 []) witnessesT8H28 = true := by rfl
end SpectreClusters.StageD.Raw
