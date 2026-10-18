module

public import SpectreClusters.StageABindingCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem candidateB_cell7_check :
    (rawNeighborsAt ⟨(1,-1),2⟩).all (candidateCheckB .turtle) = true := by
  rfl
end SpectreClusters.StageA
