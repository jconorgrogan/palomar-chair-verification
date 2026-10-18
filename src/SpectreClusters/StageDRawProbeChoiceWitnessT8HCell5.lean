module

public import SpectreClusters.StageDRawChoiceWitness
public import SpectreClusters.StageDRawProbeCandidateT8HCell21Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeChoiceWitnessT8H5_checked : witnessChoicesCheck
    ((probeChoices .t8h).getD 5 []) witnessesT8H21 = true := by rfl
end SpectreClusters.StageD.Raw
