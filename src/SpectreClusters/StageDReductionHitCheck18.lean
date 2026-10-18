module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit72_checked : allRawHitCheckB .t8h 1492471644005 = true := by rfl
theorem hit72_checked : hitCheckB kept (hitAt 72) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit72_checked
set_option maxRecDepth 100000 in
theorem rawHit73_checked : allRawHitCheckB .t8h 1492471644133 = true := by rfl
theorem hit73_checked : hitCheckB kept (hitAt 73) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit73_checked
set_option maxRecDepth 100000 in
theorem rawHit74_checked : allRawHitCheckB .t8h 1509349523429 = true := by rfl
theorem hit74_checked : hitCheckB kept (hitAt 74) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit74_checked
set_option maxRecDepth 100000 in
theorem rawHit75_checked : allRawHitCheckB .t8h 1509383069637 = true := by rfl
theorem hit75_checked : hitCheckB kept (hitAt 75) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit75_checked
end SpectreClusters.StageD.Reduction
