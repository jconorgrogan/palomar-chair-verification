module

public import SpectreClusters.StageDRawProbeT7HStep0

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT7H1 : List (List Nat) := [[35],[164]]
set_option maxRecDepth 100000 in
theorem probeSuffixT7H1_complete :
    enumerate (idCompatible .t7h) ((probeChoices .t7h).drop 5) = probeSuffixT7H1 := by
  change extend (idCompatible .t7h) [35,164]
    (enumerate (idCompatible .t7h) ((probeChoices .t7h).drop 6)) = probeSuffixT7H1
  rw [probeSuffixT7H0_complete]
  rfl
end SpectreClusters.StageD.Raw
