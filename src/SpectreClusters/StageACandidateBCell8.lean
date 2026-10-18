module

public import SpectreClusters.StageABindingCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem candidateB_cell8_check :
    (rawNeighborsAt ⟨(1,0),3⟩).all (candidateCheckB .turtle) = true := by
  rfl
end SpectreClusters.StageA
