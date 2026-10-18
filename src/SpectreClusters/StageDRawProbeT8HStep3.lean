module

public import SpectreClusters.StageDRawProbeT8HStep2

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H3 : List (List Nat) := [[1,30,30],[23,30,30],[45,30,30],[90,30,30],[114,30,30],[133,30,30],[155,30,30],[177,30,30],[222,30,30],[244,30,30],[1,118,118],[23,118,118],[90,118,118],[155,118,118],[222,118,118],[244,118,118],[1,162,162],[23,162,162],[45,162,162],[90,162,162],[114,162,162],[133,162,162],[155,162,162],[177,162,162],[222,162,162],[244,162,162],[1,206,206],[23,206,206],[90,206,206],[155,206,206],[222,206,206],[244,206,206],[1,251,251],[23,251,251],[90,251,251],[155,251,251],[222,251,251],[244,251,251]]
set_option maxRecDepth 100000 in
theorem probeSuffixT8H3_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 12) = probeSuffixT8H3 := by
  change extend (idCompatible .t8h) [1,23,45,90,114,133,155,177,222,244]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 13)) = probeSuffixT8H3
  rw [probeSuffixT8H2_complete]
  rfl
end SpectreClusters.StageD.Raw
