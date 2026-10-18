module

public import SpectreClusters.StageDRawProbeT8HStep13InputSplits
public import SpectreClusters.StageDRawProbeT8HStep12Chunk2
public import SpectreClusters.StageDRawProbeT8HStep13Chunk8
public import SpectreClusters.StageDRawProbeT8HStep13Chunk9
public import SpectreClusters.StageDRawProbeT8HStep13Chunk10

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeOutputT8H12Chunk2_input_binding :
    probeOutputT8H12Chunk2 = probeInputT8H13Chunk7Right ++ probeInputT8H13Chunk8 ++ probeInputT8H13Chunk9 ++ probeInputT8H13Chunk10 ++ probeInputT8H13Chunk11Left := by
  rfl
end SpectreClusters.StageD.Raw
