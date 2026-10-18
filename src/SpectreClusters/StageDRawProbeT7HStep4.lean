module

public import SpectreClusters.StageDRawProbeT7HStep3

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT7H4 : List (List Nat) := [[98,126,49,35],[229,126,49,35],[98,258,49,35],[229,258,49,35],[98,126,179,35],[229,126,179,35],[98,258,179,35],[229,258,179,35],[98,126,49,164],[229,126,49,164],[98,258,49,164],[229,258,49,164],[98,126,179,164],[229,126,179,164],[98,258,179,164],[229,258,179,164]]
set_option maxRecDepth 100000 in
theorem probeSuffixT7H4_complete :
    enumerate (idCompatible .t7h) ((probeChoices .t7h).drop 2) = probeSuffixT7H4 := by
  change extend (idCompatible .t7h) [15,34,36,38,54,57,79,83,98,101,104,121,125,142,145,165,168,184,187,190,209,213,229,232,235,253,257]
    (enumerate (idCompatible .t7h) ((probeChoices .t7h).drop 3)) = probeSuffixT7H4
  rw [probeSuffixT7H3_complete]
  rfl
end SpectreClusters.StageD.Raw
