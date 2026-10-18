module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit16_checked : allRawHitCheckB .t7h 10356 = true := by rfl
theorem hit16_checked : hitCheckB kept (hitAt 16) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit16_checked
set_option maxRecDepth 100000 in
theorem rawHit17_checked : allRawHitCheckB .t7h 10485 = true := by rfl
theorem hit17_checked : hitCheckB kept (hitAt 17) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit17_checked
set_option maxRecDepth 100000 in
theorem rawHit18_checked : allRawHitCheckB .t7h 10530 = true := by rfl
theorem hit18_checked : hitCheckB kept (hitAt 18) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit18_checked
set_option maxRecDepth 100000 in
theorem rawHit19_checked : allRawHitCheckB .t7h 10546 = true := by rfl
theorem hit19_checked : hitCheckB kept (hitAt 19) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit19_checked
end SpectreClusters.StageD.Reduction
