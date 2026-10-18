module

public import SpectreClusters.StageDRawProbeT8HStep13
public import SpectreClusters.StageDRawProbeT8HStep14Chunk0
public import SpectreClusters.StageDRawProbeT8HStep14Chunk1
public import SpectreClusters.StageDRawProbeT8HStep14Chunk2
public import SpectreClusters.StageDRawProbeT8HStep14Chunk3
public import SpectreClusters.StageDRawProbeT8HStep14Chunk4
public import SpectreClusters.StageDRawProbeT8HStep14Chunk5
public import SpectreClusters.StageDRawProbeT8HStep14Chunk6
public import SpectreClusters.StageDRawProbeT8HStep14Chunk7
public import SpectreClusters.StageDRawProbeT8HStep14Chunk8
public import SpectreClusters.StageDRawProbeT8HStep14Chunk9
public import SpectreClusters.StageDRawProbeT8HStep14Chunk10
public import SpectreClusters.StageDRawProbeT8HStep14Chunk11
public import SpectreClusters.StageDRawProbeT8HStep14Chunk12
public import SpectreClusters.StageDRawProbeT8HStep14Chunk13
public import SpectreClusters.StageDRawProbeT8HStep14Chunk14
public import SpectreClusters.StageDRawProbeT8HStep14Chunk15
public import SpectreClusters.StageDRawProbeT8HStep14Chunk16
public import SpectreClusters.StageDRawProbeT8HStep14Chunk17
public import SpectreClusters.StageDRawProbeT8HStep14InputRefinement

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H14 : List (List Nat) := probeOutputT8H14Chunk0 ++ probeOutputT8H14Chunk1 ++ probeOutputT8H14Chunk2 ++ probeOutputT8H14Chunk3 ++ probeOutputT8H14Chunk4 ++ probeOutputT8H14Chunk5 ++ probeOutputT8H14Chunk6 ++ probeOutputT8H14Chunk7 ++ probeOutputT8H14Chunk8 ++ probeOutputT8H14Chunk9 ++ probeOutputT8H14Chunk10 ++ probeOutputT8H14Chunk11 ++ probeOutputT8H14Chunk12 ++ probeOutputT8H14Chunk13 ++ probeOutputT8H14Chunk14 ++ probeOutputT8H14Chunk15 ++ probeOutputT8H14Chunk16 ++ probeOutputT8H14Chunk17
set_option maxRecDepth 100000 in
theorem probeSuffixT8H14_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 1) = probeSuffixT8H14 := by
  change extend (idCompatible .t8h) [12,55,77,100,123,144,165,187,209,232,256]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 2)) = probeSuffixT8H14
  rw [probeSuffixT8H13_complete]
  rw [probeSuffixT8H13_input_refinement14]
  simp only [extend_append,probeOutputT8H14Chunk0_checked,probeOutputT8H14Chunk1_checked,probeOutputT8H14Chunk2_checked,probeOutputT8H14Chunk3_checked,probeOutputT8H14Chunk4_checked,probeOutputT8H14Chunk5_checked,probeOutputT8H14Chunk6_checked,probeOutputT8H14Chunk7_checked,probeOutputT8H14Chunk8_checked,probeOutputT8H14Chunk9_checked,probeOutputT8H14Chunk10_checked,probeOutputT8H14Chunk11_checked,probeOutputT8H14Chunk12_checked,probeOutputT8H14Chunk13_checked,probeOutputT8H14Chunk14_checked,probeOutputT8H14Chunk15_checked,probeOutputT8H14Chunk16_checked,probeOutputT8H14Chunk17_checked,probeSuffixT8H14]
end SpectreClusters.StageD.Raw
