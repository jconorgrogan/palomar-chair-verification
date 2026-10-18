module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit0_checked : allRawHitCheckB .t7h 395 = true := by rfl
theorem hit0_checked : hitCheckB kept (hitAt 0) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit0_checked
set_option maxRecDepth 100000 in
theorem rawHit1_checked : allRawHitCheckB .t7h 628 = true := by rfl
theorem hit1_checked : hitCheckB kept (hitAt 1) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit1_checked
set_option maxRecDepth 100000 in
theorem rawHit2_checked : allRawHitCheckB .t7h 1229 = true := by rfl
theorem hit2_checked : hitCheckB kept (hitAt 2) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit2_checked
set_option maxRecDepth 100000 in
theorem rawHit3_checked : allRawHitCheckB .t7h 1677 = true := by rfl
theorem hit3_checked : hitCheckB kept (hitAt 3) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit3_checked
end SpectreClusters.StageD.Reduction
