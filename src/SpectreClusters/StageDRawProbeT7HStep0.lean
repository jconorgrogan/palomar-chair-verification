module

public import SpectreClusters.StageDRawProbeData

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT7H0 : List (List Nat) := [[]]
set_option maxRecDepth 100000 in
theorem probeSuffixT7H0_complete :
    enumerate (idCompatible .t7h) ((probeChoices .t7h).drop 6) = probeSuffixT7H0 := by
  rfl
end SpectreClusters.StageD.Raw
