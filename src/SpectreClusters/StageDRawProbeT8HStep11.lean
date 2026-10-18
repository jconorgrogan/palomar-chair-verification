module

public import SpectreClusters.StageDRawProbeT8HStep10
public import SpectreClusters.StageDRawProbeT8HStep11Chunk0
public import SpectreClusters.StageDRawProbeT8HStep11Chunk1
public import SpectreClusters.StageDRawProbeT8HStep11Chunk2
public import SpectreClusters.StageDRawProbeT8HStep11Chunk3
public import SpectreClusters.StageDRawProbeT8HStep11Chunk4
public import SpectreClusters.StageDRawProbeT8HStep11Chunk5

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H11 : List (List Nat) := probeOutputT8H11Chunk0 ++ probeOutputT8H11Chunk1 ++ probeOutputT8H11Chunk2 ++ probeOutputT8H11Chunk3 ++ probeOutputT8H11Chunk4 ++ probeOutputT8H11Chunk5
set_option maxRecDepth 100000 in
theorem probeSuffixT8H11_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 4) = probeSuffixT8H11 := by
  change extend (idCompatible .t8h) [40,85,107,128,172,194,217,239,261]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 5)) = probeSuffixT8H11
  rw [probeSuffixT8H10_complete]
  change extend (idCompatible .t8h) [40,85,107,128,172,194,217,239,261] (probeInputT8H11Chunk0 ++ probeInputT8H11Chunk1 ++ probeInputT8H11Chunk2 ++ probeInputT8H11Chunk3 ++ probeInputT8H11Chunk4 ++ probeInputT8H11Chunk5) = probeSuffixT8H11
  simp only [extend_append,probeOutputT8H11Chunk0_checked,probeOutputT8H11Chunk1_checked,probeOutputT8H11Chunk2_checked,probeOutputT8H11Chunk3_checked,probeOutputT8H11Chunk4_checked,probeOutputT8H11Chunk5_checked,probeSuffixT8H11]
end SpectreClusters.StageD.Raw
