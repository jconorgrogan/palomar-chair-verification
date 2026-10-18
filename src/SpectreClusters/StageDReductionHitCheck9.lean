module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit36_checked : allRawHitCheckB .t7h 15028 = true := by rfl
theorem hit36_checked : hitCheckB kept (hitAt 36) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit36_checked
set_option maxRecDepth 100000 in
theorem rawHit37_checked : allRawHitCheckB .t7h 15088 = true := by rfl
theorem hit37_checked : hitCheckB kept (hitAt 37) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit37_checked
set_option maxRecDepth 100000 in
theorem rawHit38_checked : allRawHitCheckB .t7h 15093 = true := by rfl
theorem hit38_checked : hitCheckB kept (hitAt 38) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit38_checked
set_option maxRecDepth 100000 in
theorem rawHit39_checked : allRawHitCheckB .t7h 16125 = true := by rfl
theorem hit39_checked : hitCheckB kept (hitAt 39) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit39_checked
end SpectreClusters.StageD.Reduction
