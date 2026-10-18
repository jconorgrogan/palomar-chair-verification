module

public import SpectreClusters.StageDRawProbeT8HStep14
public import SpectreClusters.StageDRawProbeT8HStep15Chunk0
public import SpectreClusters.StageDRawProbeT8HStep15Chunk1
public import SpectreClusters.StageDRawProbeT8HStep15Chunk2
public import SpectreClusters.StageDRawProbeT8HStep15Chunk3
public import SpectreClusters.StageDRawProbeT8HStep15Chunk4
public import SpectreClusters.StageDRawProbeT8HStep15Chunk5
public import SpectreClusters.StageDRawProbeT8HStep15Chunk6
public import SpectreClusters.StageDRawProbeT8HStep15Chunk7
public import SpectreClusters.StageDRawProbeT8HStep15Chunk8
public import SpectreClusters.StageDRawProbeT8HStep15Chunk9
public import SpectreClusters.StageDRawProbeT8HStep15Chunk10
public import SpectreClusters.StageDRawProbeT8HStep15Chunk11
public import SpectreClusters.StageDRawProbeT8HStep15Chunk12
public import SpectreClusters.StageDRawProbeT8HStep15Chunk13
public import SpectreClusters.StageDRawProbeT8HStep15Chunk14
public import SpectreClusters.StageDRawProbeT8HStep15InputRefinement

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H15 : List (List Nat) := probeOutputT8H15Chunk0 ++ probeOutputT8H15Chunk1 ++ probeOutputT8H15Chunk2 ++ probeOutputT8H15Chunk3 ++ probeOutputT8H15Chunk4 ++ probeOutputT8H15Chunk5 ++ probeOutputT8H15Chunk6 ++ probeOutputT8H15Chunk7 ++ probeOutputT8H15Chunk8 ++ probeOutputT8H15Chunk9 ++ probeOutputT8H15Chunk10 ++ probeOutputT8H15Chunk11 ++ probeOutputT8H15Chunk12 ++ probeOutputT8H15Chunk13 ++ probeOutputT8H15Chunk14
set_option maxRecDepth 100000 in
theorem probeSuffixT8H15_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 0) = probeSuffixT8H15 := by
  change extend (idCompatible .t8h) [15,35,36,39,55,58,80,84,100,103,106,123,127,144,147,167,171,187,190,193,212,216,232,235,238,256,260]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 1)) = probeSuffixT8H15
  rw [probeSuffixT8H14_complete]
  rw [probeSuffixT8H14_input_refinement15]
  simp only [extend_append,probeOutputT8H15Chunk0_checked,probeOutputT8H15Chunk1_checked,probeOutputT8H15Chunk2_checked,probeOutputT8H15Chunk3_checked,probeOutputT8H15Chunk4_checked,probeOutputT8H15Chunk5_checked,probeOutputT8H15Chunk6_checked,probeOutputT8H15Chunk7_checked,probeOutputT8H15Chunk8_checked,probeOutputT8H15Chunk9_checked,probeOutputT8H15Chunk10_checked,probeOutputT8H15Chunk11_checked,probeOutputT8H15Chunk12_checked,probeOutputT8H15Chunk13_checked,probeOutputT8H15Chunk14_checked,probeSuffixT8H15]
end SpectreClusters.StageD.Raw
