module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit8_checked : allRawHitCheckB .t7h 8031 = true := by rfl
theorem hit8_checked : hitCheckB kept (hitAt 8) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit8_checked
set_option maxRecDepth 100000 in
theorem rawHit9_checked : allRawHitCheckB .t7h 8159 = true := by rfl
theorem hit9_checked : hitCheckB kept (hitAt 9) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit9_checked
set_option maxRecDepth 100000 in
theorem rawHit10_checked : allRawHitCheckB .t7h 8566 = true := by rfl
theorem hit10_checked : hitCheckB kept (hitAt 10) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit10_checked
set_option maxRecDepth 100000 in
theorem rawHit11_checked : allRawHitCheckB .t7h 8788 = true := by rfl
theorem hit11_checked : hitCheckB kept (hitAt 11) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit11_checked
end SpectreClusters.StageD.Reduction
