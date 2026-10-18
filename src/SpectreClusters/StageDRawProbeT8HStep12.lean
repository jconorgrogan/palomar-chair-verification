module

public import SpectreClusters.StageDRawProbeT8HStep11
public import SpectreClusters.StageDRawProbeT8HStep12Chunk0
public import SpectreClusters.StageDRawProbeT8HStep12Chunk1
public import SpectreClusters.StageDRawProbeT8HStep12Chunk2
public import SpectreClusters.StageDRawProbeT8HStep12Chunk3
public import SpectreClusters.StageDRawProbeT8HStep12Chunk4
public import SpectreClusters.StageDRawProbeT8HStep12Chunk5
public import SpectreClusters.StageDRawProbeT8HStep12Chunk6

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H12 : List (List Nat) := probeOutputT8H12Chunk0 ++ probeOutputT8H12Chunk1 ++ probeOutputT8H12Chunk2 ++ probeOutputT8H12Chunk3 ++ probeOutputT8H12Chunk4 ++ probeOutputT8H12Chunk5 ++ probeOutputT8H12Chunk6
set_option maxRecDepth 100000 in
theorem probeSuffixT8H12_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 3) = probeSuffixT8H12 := by
  change extend (idCompatible .t8h) [35,39,55,84,106,123,127,128,144,171,187,193,216,217,238,256,260,261]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 4)) = probeSuffixT8H12
  rw [probeSuffixT8H11_complete]
  change extend (idCompatible .t8h) [35,39,55,84,106,123,127,128,144,171,187,193,216,217,238,256,260,261] (probeInputT8H12Chunk0 ++ probeInputT8H12Chunk1 ++ probeInputT8H12Chunk2 ++ probeInputT8H12Chunk3 ++ probeInputT8H12Chunk4 ++ probeInputT8H12Chunk5 ++ probeInputT8H12Chunk6) = probeSuffixT8H12
  simp only [extend_append,probeOutputT8H12Chunk0_checked,probeOutputT8H12Chunk1_checked,probeOutputT8H12Chunk2_checked,probeOutputT8H12Chunk3_checked,probeOutputT8H12Chunk4_checked,probeOutputT8H12Chunk5_checked,probeOutputT8H12Chunk6_checked,probeSuffixT8H12]
end SpectreClusters.StageD.Raw
