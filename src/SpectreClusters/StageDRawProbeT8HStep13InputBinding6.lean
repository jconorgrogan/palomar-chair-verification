module

public import SpectreClusters.StageDRawProbeT8HStep13InputSplits
public import SpectreClusters.StageDRawProbeT8HStep12Chunk6
public import SpectreClusters.StageDRawProbeT8HStep13Chunk24
public import SpectreClusters.StageDRawProbeT8HStep13Chunk25
public import SpectreClusters.StageDRawProbeT8HStep13Chunk26

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeOutputT8H12Chunk6_input_binding :
    probeOutputT8H12Chunk6 = probeInputT8H13Chunk23Right ++ probeInputT8H13Chunk24 ++ probeInputT8H13Chunk25 ++ probeInputT8H13Chunk26 := by
  rfl
end SpectreClusters.StageD.Raw
