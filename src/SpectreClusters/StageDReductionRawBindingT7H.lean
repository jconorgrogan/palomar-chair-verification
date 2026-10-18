module

public import SpectreClusters.StageDReductionRawBindingData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
theorem raw_rows_T7H_binding :
    (compactRowIDs .t7h).map (List.map (originalID .t7h)) = Raw.rawNeighborIDs .t7h := by rfl
end SpectreClusters.StageD.Reduction
