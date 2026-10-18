module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart0
public import SpectreClusters.StageAReject0BPart1
public import SpectreClusters.StageAReject0BPart2
public import SpectreClusters.StageAReject0BPart3

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_0 : retentionCheckB 0 .turtle 0 = true :=
  retention_of_kept 0 .turtle 0 (by rfl)
theorem retention0B_1 : retentionCheckB 0 .turtle 1 = true :=
  retention_of_rejected 0 .turtle 1 reject0B_1
theorem retention0B_2 : retentionCheckB 0 .turtle 2 = true :=
  retention_of_rejected 0 .turtle 2 reject0B_2
theorem retention0B_3 : retentionCheckB 0 .turtle 3 = true :=
  retention_of_rejected 0 .turtle 3 reject0B_3
theorem retention0B_4 : retentionCheckB 0 .turtle 4 = true :=
  retention_of_rejected 0 .turtle 4 reject0B_4
theorem retention0B_5 : retentionCheckB 0 .turtle 5 = true :=
  retention_of_rejected 0 .turtle 5 reject0B_5
theorem retention0B_6 : retentionCheckB 0 .turtle 6 = true :=
  retention_of_rejected 0 .turtle 6 reject0B_6
theorem retention0B_7 : retentionCheckB 0 .turtle 7 = true :=
  retention_of_rejected 0 .turtle 7 reject0B_7
theorem retention0B_8 : retentionCheckB 0 .turtle 8 = true :=
  retention_of_rejected 0 .turtle 8 reject0B_8
theorem retention0B_9 : retentionCheckB 0 .turtle 9 = true :=
  retention_of_rejected 0 .turtle 9 reject0B_9
theorem retention0B_10 : retentionCheckB 0 .turtle 10 = true :=
  retention_of_rejected 0 .turtle 10 reject0B_10
theorem retention0B_11 : retentionCheckB 0 .turtle 11 = true :=
  retention_of_rejected 0 .turtle 11 reject0B_11
theorem retention0B_12 : retentionCheckB 0 .turtle 12 = true :=
  retention_of_rejected 0 .turtle 12 reject0B_12
theorem retention0B_13 : retentionCheckB 0 .turtle 13 = true :=
  retention_of_rejected 0 .turtle 13 reject0B_13
theorem retention0B_14 : retentionCheckB 0 .turtle 14 = true :=
  retention_of_rejected 0 .turtle 14 reject0B_14
theorem retention0B_15 : retentionCheckB 0 .turtle 15 = true :=
  retention_of_rejected 0 .turtle 15 reject0B_15
theorem retention0B_block0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_0, retention0B_1, retention0B_2, retention0B_3, retention0B_4, retention0B_5, retention0B_6, retention0B_7, retention0B_8, retention0B_9, retention0B_10, retention0B_11, retention0B_12, retention0B_13, retention0B_14, retention0B_15] <;> rfl
end SpectreClusters.StageA
