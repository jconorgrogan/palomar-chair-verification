module

public import SpectreClusters.StageDRawProbeT8HStep3

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H4 : List (List Nat) := [[45,45,30,30],[114,114,30,30],[133,133,30,30],[177,177,30,30],[118,1,118,118],[118,23,118,118],[118,90,118,118],[118,155,118,118],[118,222,118,118],[118,244,118,118],[45,45,162,162],[114,114,162,162],[133,133,162,162],[177,177,162,162],[206,1,206,206],[206,23,206,206],[206,90,206,206],[206,155,206,206],[206,222,206,206],[206,244,206,206],[251,1,251,251],[251,23,251,251],[251,90,251,251],[251,155,251,251],[251,222,251,251],[251,244,251,251]]
set_option maxRecDepth 100000 in
theorem probeSuffixT8H4_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 11) = probeSuffixT8H4 := by
  change extend (idCompatible .t8h) [2,3,4,24,25,45,46,47,50,68,69,91,92,96,112,114,118,133,134,135,136,156,157,177,178,179,182,200,201,206,223,224,225,245,246,251]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 12)) = probeSuffixT8H4
  rw [probeSuffixT8H3_complete]
  rfl
end SpectreClusters.StageD.Raw
