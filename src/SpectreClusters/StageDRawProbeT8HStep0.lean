module

public import SpectreClusters.StageDRawProbeData

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H0 : List (List Nat) := [[]]
set_option maxRecDepth 100000 in
theorem probeSuffixT8H0_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 15) = probeSuffixT8H0 := by
  rfl
end SpectreClusters.StageD.Raw
