module

public import SpectreClusters.StageABindingCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem candidateA_cell5_check :
    (rawNeighborsAt ⟨(1,-1),1⟩).all (candidateCheckB .hat) = true := by
  rfl
end SpectreClusters.StageA
