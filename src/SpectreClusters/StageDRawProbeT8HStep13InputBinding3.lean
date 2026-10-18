module

public import SpectreClusters.StageDRawProbeT8HStep13InputSplits
public import SpectreClusters.StageDRawProbeT8HStep12Chunk3
public import SpectreClusters.StageDRawProbeT8HStep13Chunk12
public import SpectreClusters.StageDRawProbeT8HStep13Chunk13
public import SpectreClusters.StageDRawProbeT8HStep13Chunk14

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeOutputT8H12Chunk3_input_binding :
    probeOutputT8H12Chunk3 = probeInputT8H13Chunk11Right ++ probeInputT8H13Chunk12 ++ probeInputT8H13Chunk13 ++ probeInputT8H13Chunk14 ++ probeInputT8H13Chunk15Left := by
  rfl
end SpectreClusters.StageD.Raw
