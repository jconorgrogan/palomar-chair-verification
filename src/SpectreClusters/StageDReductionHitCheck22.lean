module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel
public import SpectreClusters.StageDReductionRetainedRowBindings

@[expose] public section

namespace SpectreClusters.StageD.Reduction
theorem hit88_checked : hitCheckB kept (hitAt 88) = true := by
  change [139,140].all (fun i => (compactIDs .t7h i).any (fun m => decide (m < (compactCandidates .t7h).length) && (2245 : Nat).testBit m)) = true
  simp only [List.all_cons,List.all_nil,retained_t7h_row_139_ids,retained_t7h_row_140_ids] <;> rfl
end SpectreClusters.StageD.Reduction
