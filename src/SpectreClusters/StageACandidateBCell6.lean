module

public import SpectreClusters.StageABindingCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem candidateB_cell6_check :
    (rawNeighborsAt ⟨(1,-1),1⟩).all (candidateCheckB .turtle) = true := by
  rfl
end SpectreClusters.StageA
