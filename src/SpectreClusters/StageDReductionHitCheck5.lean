module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit20_checked : allRawHitCheckB .t7h 10598 = true := by rfl
theorem hit20_checked : hitCheckB kept (hitAt 20) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit20_checked
set_option maxRecDepth 100000 in
theorem rawHit21_checked : allRawHitCheckB .t7h 10614 = true := by rfl
theorem hit21_checked : hitCheckB kept (hitAt 21) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit21_checked
set_option maxRecDepth 100000 in
theorem rawHit22_checked : allRawHitCheckB .t7h 10804 = true := by rfl
theorem hit22_checked : hitCheckB kept (hitAt 22) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit22_checked
set_option maxRecDepth 100000 in
theorem rawHit23_checked : allRawHitCheckB .t7h 10864 = true := by rfl
theorem hit23_checked : hitCheckB kept (hitAt 23) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit23_checked
end SpectreClusters.StageD.Reduction
