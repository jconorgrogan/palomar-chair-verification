module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit28_checked : allRawHitCheckB .t7h 11122 = true := by rfl
theorem hit28_checked : hitCheckB kept (hitAt 28) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit28_checked
set_option maxRecDepth 100000 in
theorem rawHit29_checked : allRawHitCheckB .t7h 11126 = true := by rfl
theorem hit29_checked : hitCheckB kept (hitAt 29) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit29_checked
set_option maxRecDepth 100000 in
theorem rawHit30_checked : allRawHitCheckB .t7h 13611 = true := by rfl
theorem hit30_checked : hitCheckB kept (hitAt 30) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit30_checked
set_option maxRecDepth 100000 in
theorem rawHit31_checked : allRawHitCheckB .t7h 13738 = true := by rfl
theorem hit31_checked : hitCheckB kept (hitAt 31) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit31_checked
end SpectreClusters.StageD.Reduction
