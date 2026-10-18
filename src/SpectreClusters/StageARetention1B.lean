module

public import SpectreClusters.StageARetention1BBlock0
public import SpectreClusters.StageARetention1BBlock1

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention1B_all : (keptIds 1 .turtle).all (retentionCheckB 1 .turtle) = true := by
  have hp : keptIds 1 .turtle = [0,52,163,171,179,183,201,203,205,206,207,208,212,214,215,216] ++ [219,221,222,223,226,227,229,231,240,242,244,246,248,250] := by rfl
  rw [hp]
  simp only [List.all_append]
  rw [retention1B_block0, retention1B_block1] <;> rfl
end SpectreClusters.StageA
