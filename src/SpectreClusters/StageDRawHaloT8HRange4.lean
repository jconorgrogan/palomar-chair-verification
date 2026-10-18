module

public import SpectreClusters.StageDRawHaloRanges

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem haloT8HRange4_checked : haloRangeCheck (clusterCells .t8h) (haloOrder .t8h) 32 = true := by rfl
end SpectreClusters.StageD.Raw
