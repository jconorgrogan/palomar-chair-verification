module

public import SpectreClusters.StageDRawProbeT8HStep13InputSplits
public import SpectreClusters.StageDRawProbeT8HStep12Chunk0
public import SpectreClusters.StageDRawProbeT8HStep13Chunk0
public import SpectreClusters.StageDRawProbeT8HStep13Chunk1
public import SpectreClusters.StageDRawProbeT8HStep13Chunk2

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeOutputT8H12Chunk0_input_binding :
    probeOutputT8H12Chunk0 = probeInputT8H13Chunk0 ++ probeInputT8H13Chunk1 ++ probeInputT8H13Chunk2 ++ probeInputT8H13Chunk3Left := by
  rfl
end SpectreClusters.StageD.Raw
