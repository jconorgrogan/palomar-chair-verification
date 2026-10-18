module

public import SpectreClusters.StageABindingCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem candidateB_cell4_check :
    (rawNeighborsAt ⟨(0,0),4⟩).all (candidateCheckB .turtle) = true := by
  rfl
end SpectreClusters.StageA
