module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit76_checked : allRawHitCheckB .t8h 1509517291493 = true := by rfl
theorem hit76_checked : hitCheckB kept (hitAt 76) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit76_checked
set_option maxRecDepth 100000 in
theorem rawHit77_checked : allRawHitCheckB .t8h 1509651509093 = true := by rfl
theorem hit77_checked : hitCheckB kept (hitAt 77) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit77_checked
set_option maxRecDepth 100000 in
theorem rawHit78_checked : allRawHitCheckB .t8h 1740329218873 = true := by rfl
theorem hit78_checked : hitCheckB kept (hitAt 78) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit78_checked
set_option maxRecDepth 100000 in
theorem rawHit79_checked : allRawHitCheckB .t8h 1756418695993 = true := by rfl
theorem hit79_checked : hitCheckB kept (hitAt 79) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit79_checked
end SpectreClusters.StageD.Reduction
