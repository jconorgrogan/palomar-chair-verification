module

public import SpectreClusters.StageDRawHaloRanges

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem haloT8HRange0_checked : haloRangeCheck (clusterCells .t8h) (haloOrder .t8h) 0 = true := by rfl
end SpectreClusters.StageD.Raw
