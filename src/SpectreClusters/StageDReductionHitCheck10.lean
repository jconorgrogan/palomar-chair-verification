module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit40_checked : allRawHitCheckB .t8h 111258296953 = true := by rfl
theorem hit40_checked : hitCheckB kept (hitAt 40) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit40_checked
set_option maxRecDepth 100000 in
theorem rawHit41_checked : allRawHitCheckB .t8h 306454551460 = true := by rfl
theorem hit41_checked : hitCheckB kept (hitAt 41) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit41_checked
set_option maxRecDepth 100000 in
theorem rawHit42_checked : allRawHitCheckB .t8h 374100286372 = true := by rfl
theorem hit42_checked : hitCheckB kept (hitAt 42) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit42_checked
set_option maxRecDepth 100000 in
theorem rawHit43_checked : allRawHitCheckB .t8h 375174011812 = true := by rfl
theorem hit43_checked : hitCheckB kept (hitAt 43) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit43_checked
end SpectreClusters.StageD.Reduction
