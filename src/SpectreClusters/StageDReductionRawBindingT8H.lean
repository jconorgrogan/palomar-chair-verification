module

public import SpectreClusters.StageDReductionRawBindingData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
theorem raw_rows_T8H_binding :
    (compactRowIDs .t8h).map (List.map (originalID .t8h)) = Raw.rawNeighborIDs .t8h := by rfl
end SpectreClusters.StageD.Reduction
