module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit60_checked : allRawHitCheckB .t8h 835585281230 = true := by rfl
theorem hit60_checked : hitCheckB kept (hitAt 60) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit60_checked
set_option maxRecDepth 100000 in
theorem rawHit61_checked : allRawHitCheckB .t8h 835585805390 = true := by rfl
theorem hit61_checked : hitCheckB kept (hitAt 61) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit61_checked
set_option maxRecDepth 100000 in
theorem rawHit62_checked : allRawHitCheckB .t8h 973020040398 = true := by rfl
theorem hit62_checked : hitCheckB kept (hitAt 62) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit62_checked
set_option maxRecDepth 100000 in
theorem rawHit63_checked : allRawHitCheckB .t8h 973020564558 = true := by rfl
theorem hit63_checked : hitCheckB kept (hitAt 63) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit63_checked
end SpectreClusters.StageD.Reduction
