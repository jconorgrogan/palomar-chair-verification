module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit64_checked : allRawHitCheckB .t8h 1157276922673 = true := by rfl
theorem hit64_checked : hitCheckB kept (hitAt 64) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit64_checked
set_option maxRecDepth 100000 in
theorem rawHit65_checked : allRawHitCheckB .t8h 1224922657585 = true := by rfl
theorem hit65_checked : hitCheckB kept (hitAt 65) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit65_checked
set_option maxRecDepth 100000 in
theorem rawHit66_checked : allRawHitCheckB .t8h 1405764886500 = true := by rfl
theorem hit66_checked : hitCheckB kept (hitAt 66) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit66_checked
set_option maxRecDepth 100000 in
theorem rawHit67_checked : allRawHitCheckB .t8h 1473410621412 = true := by rfl
theorem hit67_checked : hitCheckB kept (hitAt 67) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit67_checked
end SpectreClusters.StageD.Reduction
