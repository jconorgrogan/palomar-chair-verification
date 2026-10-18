module

public import SpectreClusters.StageDRawHaloRanges

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem haloT7HRange9_checked : haloRangeCheck (clusterCells .t7h) (haloOrder .t7h) 72 = true := by rfl
end SpectreClusters.StageD.Raw
