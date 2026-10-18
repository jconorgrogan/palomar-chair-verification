module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit68_checked : allRawHitCheckB .t8h 1474484346852 = true := by rfl
theorem hit68_checked : hitCheckB kept (hitAt 68) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit68_checked
set_option maxRecDepth 100000 in
theorem rawHit69_checked : allRawHitCheckB .t8h 1488176676837 = true := by rfl
theorem hit69_checked : hitCheckB kept (hitAt 69) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit69_checked
set_option maxRecDepth 100000 in
theorem rawHit70_checked : allRawHitCheckB .t8h 1492337426405 = true := by rfl
theorem hit70_checked : hitCheckB kept (hitAt 70) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit70_checked
set_option maxRecDepth 100000 in
theorem rawHit71_checked : allRawHitCheckB .t8h 1492471119845 = true := by rfl
theorem hit71_checked : hitCheckB kept (hitAt 71) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit71_checked
end SpectreClusters.StageD.Reduction
