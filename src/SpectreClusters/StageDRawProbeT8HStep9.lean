module

public import SpectreClusters.StageDRawProbeT8HStep8
public import SpectreClusters.StageDRawProbeT8HStep9Chunk0
public import SpectreClusters.StageDRawProbeT8HStep9Chunk1
public import SpectreClusters.StageDRawProbeT8HStep9Chunk2

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H9 : List (List Nat) := probeOutputT8H9Chunk0 ++ probeOutputT8H9Chunk1 ++ probeOutputT8H9Chunk2
set_option maxRecDepth 100000 in
theorem probeSuffixT8H9_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 6) = probeSuffixT8H9 := by
  change extend (idCompatible .t8h) [16,37,41,59,86,104,108,129,148,168,173,191,195,218,236,240,262]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 7)) = probeSuffixT8H9
  rw [probeSuffixT8H8_complete]
  change extend (idCompatible .t8h) [16,37,41,59,86,104,108,129,148,168,173,191,195,218,236,240,262] (probeInputT8H9Chunk0 ++ probeInputT8H9Chunk1 ++ probeInputT8H9Chunk2) = probeSuffixT8H9
  simp only [extend_append,probeOutputT8H9Chunk0_checked,probeOutputT8H9Chunk1_checked,probeOutputT8H9Chunk2_checked,probeSuffixT8H9]
end SpectreClusters.StageD.Raw
