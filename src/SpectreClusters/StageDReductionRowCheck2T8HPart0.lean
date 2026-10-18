module

public import SpectreClusters.StageDReductionLiteralReplay

@[expose] public section

namespace SpectreClusters.StageD.Reduction
private theorem row_step_727 : stepCheckB tables 2 .t8h 727 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_729 : stepCheckB tables 2 .t8h 729 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_753 : stepCheckB tables 2 .t8h 753 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_759 : stepCheckB tables 2 .t8h 759 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1237 : stepCheckB tables 2 .t8h 1237 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1253 : stepCheckB tables 2 .t8h 1253 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1267 : stepCheckB tables 2 .t8h 1267 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1275 : stepCheckB tables 2 .t8h 1275 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
set_option maxRecDepth 100000 in
private theorem row_ids_1289 : compactIDs .t8h 1289 = [32,12,4,7,22,31] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_1289 : packedCertificateAt 2 .t8h 1289 = ⟨12,2245,402403006536822564416005091325116731,88⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_1289 : literalCertificateCheckB tables 2 .t8h [32,12,4,7,22,31] ⟨12,2245,402403006536822564416005091325116731,88⟩ = true := by rfl
private theorem row_step_1289 : stepCheckB tables 2 .t8h 1289 = true :=
  stepCheckB_of_literal 2 .t8h 1289 [32,12,4,7,22,31] ⟨12,2245,402403006536822564416005091325116731,88⟩ row_ids_1289 row_pack_1289 row_literal_1289
private theorem row_step_1627 : stepCheckB tables 2 .t8h 1627 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1628 : stepCheckB tables 2 .t8h 1628 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1651 : stepCheckB tables 2 .t8h 1651 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1652 : stepCheckB tables 2 .t8h 1652 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1716 : stepCheckB tables 2 .t8h 1716 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1732 : stepCheckB tables 2 .t8h 1732 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1747 : stepCheckB tables 2 .t8h 1747 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1748 : stepCheckB tables 2 .t8h 1748 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1755 : stepCheckB tables 2 .t8h 1755 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_1756 : stepCheckB tables 2 .t8h 1756 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
theorem rowPart2T8H0_checked : [727,729,753,759,1237,1253,1267,1275,1289,1627,1628,1651,1652,1716,1732,1747,1748,1755,1756].all (stepCheckB tables 2 .t8h) = true := by
  simp only [List.all_cons,List.all_nil,row_step_727,row_step_729,row_step_753,row_step_759,row_step_1237,row_step_1253,row_step_1267,row_step_1275,row_step_1289,row_step_1627,row_step_1628,row_step_1651,row_step_1652,row_step_1716,row_step_1732,row_step_1747,row_step_1748,row_step_1755,row_step_1756,Bool.true_and]
end SpectreClusters.StageD.Reduction
