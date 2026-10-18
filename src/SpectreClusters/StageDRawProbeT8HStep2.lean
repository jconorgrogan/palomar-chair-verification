module

public import SpectreClusters.StageDRawProbeT8HStep1

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H2 : List (List Nat) := [[2,9],[24,9],[46,9],[91,9],[134,9],[156,9],[178,9],[223,9],[245,9],[30,30],[2,74],[118,118],[2,141],[24,141],[46,141],[91,141],[134,141],[156,141],[178,141],[223,141],[245,141],[162,162],[206,206],[2,229],[24,229],[46,229],[91,229],[134,229],[156,229],[178,229],[223,229],[245,229],[251,251]]
set_option maxRecDepth 100000 in
theorem probeSuffixT8H2_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 13) = probeSuffixT8H2 := by
  change extend (idCompatible .t8h) [2,6,24,27,30,46,50,71,91,94,96,115,118,134,138,156,159,162,178,182,203,206,223,227,245,248,251]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 14)) = probeSuffixT8H2
  rw [probeSuffixT8H1_complete]
  rfl
end SpectreClusters.StageD.Raw
