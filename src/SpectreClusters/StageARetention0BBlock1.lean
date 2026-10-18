module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart3
public import SpectreClusters.StageAReject0BPart4
public import SpectreClusters.StageAReject0BPart5
public import SpectreClusters.StageAReject0BPart6
public import SpectreClusters.StageAReject0BPart7

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_16 : retentionCheckB 0 .turtle 16 = true :=
  retention_of_rejected 0 .turtle 16 reject0B_16
theorem retention0B_17 : retentionCheckB 0 .turtle 17 = true :=
  retention_of_rejected 0 .turtle 17 reject0B_17
theorem retention0B_18 : retentionCheckB 0 .turtle 18 = true :=
  retention_of_rejected 0 .turtle 18 reject0B_18
theorem retention0B_19 : retentionCheckB 0 .turtle 19 = true :=
  retention_of_rejected 0 .turtle 19 reject0B_19
theorem retention0B_20 : retentionCheckB 0 .turtle 20 = true :=
  retention_of_rejected 0 .turtle 20 reject0B_20
theorem retention0B_21 : retentionCheckB 0 .turtle 21 = true :=
  retention_of_rejected 0 .turtle 21 reject0B_21
theorem retention0B_22 : retentionCheckB 0 .turtle 22 = true :=
  retention_of_rejected 0 .turtle 22 reject0B_22
theorem retention0B_23 : retentionCheckB 0 .turtle 23 = true :=
  retention_of_rejected 0 .turtle 23 reject0B_23
theorem retention0B_24 : retentionCheckB 0 .turtle 24 = true :=
  retention_of_rejected 0 .turtle 24 reject0B_24
theorem retention0B_25 : retentionCheckB 0 .turtle 25 = true :=
  retention_of_rejected 0 .turtle 25 reject0B_25
theorem retention0B_26 : retentionCheckB 0 .turtle 26 = true :=
  retention_of_rejected 0 .turtle 26 reject0B_26
theorem retention0B_27 : retentionCheckB 0 .turtle 27 = true :=
  retention_of_rejected 0 .turtle 27 reject0B_27
theorem retention0B_28 : retentionCheckB 0 .turtle 28 = true :=
  retention_of_rejected 0 .turtle 28 reject0B_28
theorem retention0B_29 : retentionCheckB 0 .turtle 29 = true :=
  retention_of_rejected 0 .turtle 29 reject0B_29
theorem retention0B_30 : retentionCheckB 0 .turtle 30 = true :=
  retention_of_rejected 0 .turtle 30 reject0B_30
theorem retention0B_31 : retentionCheckB 0 .turtle 31 = true :=
  retention_of_rejected 0 .turtle 31 reject0B_31
theorem retention0B_block1 : [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_16, retention0B_17, retention0B_18, retention0B_19, retention0B_20, retention0B_21, retention0B_22, retention0B_23, retention0B_24, retention0B_25, retention0B_26, retention0B_27, retention0B_28, retention0B_29, retention0B_30, retention0B_31] <;> rfl
end SpectreClusters.StageA
