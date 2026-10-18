module

public import SpectreClusters.StageDRawProbeT8HStep0

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H1 : List (List Nat) := [[9],[30],[74],[118],[141],[162],[206],[229],[251]]
set_option maxRecDepth 100000 in
theorem probeSuffixT8H1_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 14) = probeSuffixT8H1 := by
  change extend (idCompatible .t8h) [9,30,74,118,141,162,206,229,251]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 15)) = probeSuffixT8H1
  rw [probeSuffixT8H0_complete]
  rfl
end SpectreClusters.StageD.Raw
