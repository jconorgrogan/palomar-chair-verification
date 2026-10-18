module

public import SpectreClusters.StageABindingCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem candidateA_cell4_check :
    (rawNeighborsAt ⟨(1,-1),0⟩).all (candidateCheckB .hat) = true := by
  rfl
end SpectreClusters.StageA
