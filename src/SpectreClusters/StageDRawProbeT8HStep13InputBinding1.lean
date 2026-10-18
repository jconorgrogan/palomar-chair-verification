module

public import SpectreClusters.StageDRawProbeT8HStep13InputSplits
public import SpectreClusters.StageDRawProbeT8HStep12Chunk1
public import SpectreClusters.StageDRawProbeT8HStep13Chunk4
public import SpectreClusters.StageDRawProbeT8HStep13Chunk5
public import SpectreClusters.StageDRawProbeT8HStep13Chunk6

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeOutputT8H12Chunk1_input_binding :
    probeOutputT8H12Chunk1 = probeInputT8H13Chunk3Right ++ probeInputT8H13Chunk4 ++ probeInputT8H13Chunk5 ++ probeInputT8H13Chunk6 ++ probeInputT8H13Chunk7Left := by
  rfl
end SpectreClusters.StageD.Raw
