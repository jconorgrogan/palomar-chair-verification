module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit48_checked : allRawHitCheckB .t8h 624508985977 = true := by rfl
theorem hit48_checked : hitCheckB kept (hitAt 48) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit48_checked
set_option maxRecDepth 100000 in
theorem rawHit49_checked : allRawHitCheckB .t8h 625515586105 = true := by rfl
theorem hit49_checked : hitCheckB kept (hitAt 49) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit49_checked
set_option maxRecDepth 100000 in
theorem rawHit50_checked : allRawHitCheckB .t8h 626589311545 = true := by rfl
theorem hit50_checked : hitCheckB kept (hitAt 50) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit50_checked
set_option maxRecDepth 100000 in
theorem rawHit51_checked : allRawHitCheckB .t8h 626589327929 = true := by rfl
theorem hit51_checked : hitCheckB kept (hitAt 51) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit51_checked
end SpectreClusters.StageD.Reduction
