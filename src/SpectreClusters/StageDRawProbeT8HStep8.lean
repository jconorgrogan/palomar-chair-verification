module

public import SpectreClusters.StageDRawProbeT8HStep7
public import SpectreClusters.StageDRawProbeT8HStep8Chunk0
public import SpectreClusters.StageDRawProbeT8HStep8Chunk1
public import SpectreClusters.StageDRawProbeT8HStep8Chunk2

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H8 : List (List Nat) := probeOutputT8H8Chunk0 ++ probeOutputT8H8Chunk1 ++ probeOutputT8H8Chunk2
set_option maxRecDepth 100000 in
theorem probeSuffixT8H8_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 7) = probeSuffixT8H8 := by
  change extend (idCompatible .t8h) [11,14,16,32,37,57,76,79,81,102,104,120,125,143,146,148,164,168,189,191,208,213,231,234,236,253,258]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 8)) = probeSuffixT8H8
  rw [probeSuffixT8H7_complete]
  change extend (idCompatible .t8h) [11,14,16,32,37,57,76,79,81,102,104,120,125,143,146,148,164,168,189,191,208,213,231,234,236,253,258] (probeInputT8H8Chunk0 ++ probeInputT8H8Chunk1 ++ probeInputT8H8Chunk2) = probeSuffixT8H8
  simp only [extend_append,probeOutputT8H8Chunk0_checked,probeOutputT8H8Chunk1_checked,probeOutputT8H8Chunk2_checked,probeSuffixT8H8]
end SpectreClusters.StageD.Raw
