module

public import SpectreClusters.StageABindingCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem candidateA_cell3_check :
    (rawNeighborsAt ⟨(0,0),5⟩).all (candidateCheckB .hat) = true := by
  rfl
end SpectreClusters.StageA
