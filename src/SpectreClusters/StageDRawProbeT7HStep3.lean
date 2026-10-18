module

public import SpectreClusters.StageDRawProbeT7HStep2

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT7H3 : List (List Nat) := [[126,49,35],[258,49,35],[126,179,35],[258,179,35],[126,49,164],[258,49,164],[126,179,164],[258,179,164]]
set_option maxRecDepth 100000 in
theorem probeSuffixT7H3_complete :
    enumerate (idCompatible .t7h) ((probeChoices .t7h).drop 3) = probeSuffixT7H3 := by
  change extend (idCompatible .t7h) [16,20,58,62,80,84,102,126,127,146,150,169,188,214,215,233,258,259]
    (enumerate (idCompatible .t7h) ((probeChoices .t7h).drop 4)) = probeSuffixT7H3
  rw [probeSuffixT7H2_complete]
  rfl
end SpectreClusters.StageD.Raw
