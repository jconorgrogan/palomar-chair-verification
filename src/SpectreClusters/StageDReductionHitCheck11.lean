module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit44_checked : allRawHitCheckB .t8h 443964841958 = true := by rfl
theorem hit44_checked : hitCheckB kept (hitAt 44) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit44_checked
set_option maxRecDepth 100000 in
theorem rawHit45_checked : allRawHitCheckB .t8h 511610576870 = true := by rfl
theorem hit45_checked : hitCheckB kept (hitAt 45) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit45_checked
set_option maxRecDepth 100000 in
theorem rawHit46_checked : allRawHitCheckB .t8h 512684302310 = true := by rfl
theorem hit46_checked : hitCheckB kept (hitAt 46) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit46_checked
set_option maxRecDepth 100000 in
theorem rawHit47_checked : allRawHitCheckB .t8h 557869851193 = true := by rfl
theorem hit47_checked : hitCheckB kept (hitAt 47) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit47_checked
end SpectreClusters.StageD.Reduction
