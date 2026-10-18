module

public import SpectreClusters.StageDRawProbeT8HStep13InputSplits
public import SpectreClusters.StageDRawProbeT8HStep12Chunk4
public import SpectreClusters.StageDRawProbeT8HStep13Chunk16
public import SpectreClusters.StageDRawProbeT8HStep13Chunk17
public import SpectreClusters.StageDRawProbeT8HStep13Chunk18

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeOutputT8H12Chunk4_input_binding :
    probeOutputT8H12Chunk4 = probeInputT8H13Chunk15Right ++ probeInputT8H13Chunk16 ++ probeInputT8H13Chunk17 ++ probeInputT8H13Chunk18 ++ probeInputT8H13Chunk19Left := by
  rfl
end SpectreClusters.StageD.Raw
