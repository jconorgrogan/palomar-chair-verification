module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart0
public import SpectreClusters.StageAReject0APart1

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_0 : retentionCheckB 0 .hat 0 = true :=
  retention_of_kept 0 .hat 0 (by rfl)
theorem retention0A_1 : retentionCheckB 0 .hat 1 = true :=
  retention_of_kept 0 .hat 1 (by rfl)
theorem retention0A_2 : retentionCheckB 0 .hat 2 = true :=
  retention_of_kept 0 .hat 2 (by rfl)
theorem retention0A_3 : retentionCheckB 0 .hat 3 = true :=
  retention_of_kept 0 .hat 3 (by rfl)
theorem retention0A_4 : retentionCheckB 0 .hat 4 = true :=
  retention_of_rejected 0 .hat 4 reject0A_4
theorem retention0A_5 : retentionCheckB 0 .hat 5 = true :=
  retention_of_rejected 0 .hat 5 reject0A_5
theorem retention0A_6 : retentionCheckB 0 .hat 6 = true :=
  retention_of_kept 0 .hat 6 (by rfl)
theorem retention0A_7 : retentionCheckB 0 .hat 7 = true :=
  retention_of_rejected 0 .hat 7 reject0A_7
theorem retention0A_8 : retentionCheckB 0 .hat 8 = true :=
  retention_of_kept 0 .hat 8 (by rfl)
theorem retention0A_9 : retentionCheckB 0 .hat 9 = true :=
  retention_of_rejected 0 .hat 9 reject0A_9
theorem retention0A_10 : retentionCheckB 0 .hat 10 = true :=
  retention_of_kept 0 .hat 10 (by rfl)
theorem retention0A_11 : retentionCheckB 0 .hat 11 = true :=
  retention_of_kept 0 .hat 11 (by rfl)
theorem retention0A_12 : retentionCheckB 0 .hat 12 = true :=
  retention_of_rejected 0 .hat 12 reject0A_12
theorem retention0A_13 : retentionCheckB 0 .hat 13 = true :=
  retention_of_kept 0 .hat 13 (by rfl)
theorem retention0A_14 : retentionCheckB 0 .hat 14 = true :=
  retention_of_rejected 0 .hat 14 reject0A_14
theorem retention0A_15 : retentionCheckB 0 .hat 15 = true :=
  retention_of_kept 0 .hat 15 (by rfl)
theorem retention0A_block0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_0, retention0A_1, retention0A_2, retention0A_3, retention0A_4, retention0A_5, retention0A_6, retention0A_7, retention0A_8, retention0A_9, retention0A_10, retention0A_11, retention0A_12, retention0A_13, retention0A_14, retention0A_15] <;> rfl
end SpectreClusters.StageA
