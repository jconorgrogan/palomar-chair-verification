module

public import SpectreClusters.StageDRawProbeT7HStep1

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT7H2 : List (List Nat) := [[49,35],[179,35],[49,164],[179,164]]
set_option maxRecDepth 100000 in
theorem probeSuffixT7H2_complete :
    enumerate (idCompatible .t7h) ((probeChoices .t7h).drop 4) = probeSuffixT7H2 := by
  change extend (idCompatible .t7h) [9,30,49,51,73,95,116,118,139,160,179,181,203,205,226,248,250]
    (enumerate (idCompatible .t7h) ((probeChoices .t7h).drop 5)) = probeSuffixT7H2
  rw [probeSuffixT7H1_complete]
  rfl
end SpectreClusters.StageD.Raw
