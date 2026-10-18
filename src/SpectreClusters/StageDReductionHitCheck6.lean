module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit24_checked : allRawHitCheckB .t7h 10868 = true := by rfl
theorem hit24_checked : hitCheckB kept (hitAt 24) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit24_checked
set_option maxRecDepth 100000 in
theorem rawHit25_checked : allRawHitCheckB .t7h 10933 = true := by rfl
theorem hit25_checked : hitCheckB kept (hitAt 25) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit25_checked
set_option maxRecDepth 100000 in
theorem rawHit26_checked : allRawHitCheckB .t7h 11062 = true := by rfl
theorem hit26_checked : hitCheckB kept (hitAt 26) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit26_checked
set_option maxRecDepth 100000 in
theorem rawHit27_checked : allRawHitCheckB .t7h 11106 = true := by rfl
theorem hit27_checked : hitCheckB kept (hitAt 27) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit27_checked
end SpectreClusters.StageD.Reduction
