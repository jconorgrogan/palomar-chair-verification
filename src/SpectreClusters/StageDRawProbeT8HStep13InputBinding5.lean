module

public import SpectreClusters.StageDRawProbeT8HStep13InputSplits
public import SpectreClusters.StageDRawProbeT8HStep12Chunk5
public import SpectreClusters.StageDRawProbeT8HStep13Chunk20
public import SpectreClusters.StageDRawProbeT8HStep13Chunk21
public import SpectreClusters.StageDRawProbeT8HStep13Chunk22

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeOutputT8H12Chunk5_input_binding :
    probeOutputT8H12Chunk5 = probeInputT8H13Chunk19Right ++ probeInputT8H13Chunk20 ++ probeInputT8H13Chunk21 ++ probeInputT8H13Chunk22 ++ probeInputT8H13Chunk23Left := by
  rfl
end SpectreClusters.StageD.Raw
