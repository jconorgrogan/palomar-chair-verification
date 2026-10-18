module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart11
public import SpectreClusters.StageAReject0BPart12
public import SpectreClusters.StageAReject0BPart13
public import SpectreClusters.StageAReject0BPart14
public import SpectreClusters.StageAReject0BPart15

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_48 : retentionCheckB 0 .turtle 48 = true :=
  retention_of_rejected 0 .turtle 48 reject0B_48
theorem retention0B_49 : retentionCheckB 0 .turtle 49 = true :=
  retention_of_rejected 0 .turtle 49 reject0B_49
theorem retention0B_50 : retentionCheckB 0 .turtle 50 = true :=
  retention_of_rejected 0 .turtle 50 reject0B_50
theorem retention0B_51 : retentionCheckB 0 .turtle 51 = true :=
  retention_of_rejected 0 .turtle 51 reject0B_51
theorem retention0B_52 : retentionCheckB 0 .turtle 52 = true :=
  retention_of_kept 0 .turtle 52 (by rfl)
theorem retention0B_53 : retentionCheckB 0 .turtle 53 = true :=
  retention_of_rejected 0 .turtle 53 reject0B_53
theorem retention0B_54 : retentionCheckB 0 .turtle 54 = true :=
  retention_of_rejected 0 .turtle 54 reject0B_54
theorem retention0B_55 : retentionCheckB 0 .turtle 55 = true :=
  retention_of_rejected 0 .turtle 55 reject0B_55
theorem retention0B_56 : retentionCheckB 0 .turtle 56 = true :=
  retention_of_rejected 0 .turtle 56 reject0B_56
theorem retention0B_57 : retentionCheckB 0 .turtle 57 = true :=
  retention_of_rejected 0 .turtle 57 reject0B_57
theorem retention0B_58 : retentionCheckB 0 .turtle 58 = true :=
  retention_of_rejected 0 .turtle 58 reject0B_58
theorem retention0B_59 : retentionCheckB 0 .turtle 59 = true :=
  retention_of_rejected 0 .turtle 59 reject0B_59
theorem retention0B_60 : retentionCheckB 0 .turtle 60 = true :=
  retention_of_rejected 0 .turtle 60 reject0B_60
theorem retention0B_61 : retentionCheckB 0 .turtle 61 = true :=
  retention_of_rejected 0 .turtle 61 reject0B_61
theorem retention0B_62 : retentionCheckB 0 .turtle 62 = true :=
  retention_of_rejected 0 .turtle 62 reject0B_62
theorem retention0B_63 : retentionCheckB 0 .turtle 63 = true :=
  retention_of_rejected 0 .turtle 63 reject0B_63
theorem retention0B_block3 : [48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_48, retention0B_49, retention0B_50, retention0B_51, retention0B_52, retention0B_53, retention0B_54, retention0B_55, retention0B_56, retention0B_57, retention0B_58, retention0B_59, retention0B_60, retention0B_61, retention0B_62, retention0B_63] <;> rfl
end SpectreClusters.StageA
