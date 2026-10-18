module

public import SpectreClusters.StageABindingCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem candidateA_cell6_check :
    (rawNeighborsAt ⟨(1,0),2⟩).all (candidateCheckB .hat) = true := by
  rfl
end SpectreClusters.StageA
