module

public import SpectreClusters.StageARetention1ABlock0
public import SpectreClusters.StageARetention1ABlock1

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention1A_all : (keptIds 1 .hat).all (retentionCheckB 1 .hat) = true := by
  have hp : keptIds 1 .hat = [0,1,2,3,6,8,10,11,13,15,16,17,21,22,23,24] ++ [27,28,31,32,34,35,38,39,79,81,89,91,210,246] := by rfl
  rw [hp]
  simp only [List.all_append]
  rw [retention1A_block0, retention1A_block1] <;> rfl
end SpectreClusters.StageA
