module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell44Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H13_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 13 []) witnessesT8H44 = true := by rfl
end SpectreClusters.StageD.Raw
