module

public import SpectreClusters.StageDRawProbeT8HStep9
public import SpectreClusters.StageDRawProbeT8HStep10Chunk0
public import SpectreClusters.StageDRawProbeT8HStep10Chunk1
public import SpectreClusters.StageDRawProbeT8HStep10Chunk2

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords
def probeSuffixT8H10 : List (List Nat) := probeOutputT8H10Chunk0 ++ probeOutputT8H10Chunk1 ++ probeOutputT8H10Chunk2
set_option maxRecDepth 100000 in
theorem probeSuffixT8H10_complete :
    enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 5) = probeSuffixT8H10 := by
  change extend (idCompatible .t8h) [16,20,59,63,85,104,129,148,152,172,191,217,218,236,262]
    (enumerate (idCompatible .t8h) ((probeChoices .t8h).drop 6)) = probeSuffixT8H10
  rw [probeSuffixT8H9_complete]
  change extend (idCompatible .t8h) [16,20,59,63,85,104,129,148,152,172,191,217,218,236,262] (probeInputT8H10Chunk0 ++ probeInputT8H10Chunk1 ++ probeInputT8H10Chunk2) = probeSuffixT8H10
  simp only [extend_append,probeOutputT8H10Chunk0_checked,probeOutputT8H10Chunk1_checked,probeOutputT8H10Chunk2_checked,probeSuffixT8H10]
end SpectreClusters.StageD.Raw
