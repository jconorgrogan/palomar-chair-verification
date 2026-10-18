module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell9Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H2_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 2 []) witnessesT8H9 = true := by rfl
end SpectreClusters.StageD.Raw
