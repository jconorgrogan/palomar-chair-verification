module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject1APart0

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention1A_0 : retentionCheckB 1 .hat 0 = true :=
  retention_of_kept 1 .hat 0 (by rfl)
theorem retention1A_1 : retentionCheckB 1 .hat 1 = true :=
  retention_of_rejected 1 .hat 1 reject1A_1
theorem retention1A_2 : retentionCheckB 1 .hat 2 = true :=
  retention_of_kept 1 .hat 2 (by rfl)
theorem retention1A_3 : retentionCheckB 1 .hat 3 = true :=
  retention_of_rejected 1 .hat 3 reject1A_3
theorem retention1A_6 : retentionCheckB 1 .hat 6 = true :=
  retention_of_kept 1 .hat 6 (by rfl)
theorem retention1A_8 : retentionCheckB 1 .hat 8 = true :=
  retention_of_kept 1 .hat 8 (by rfl)
theorem retention1A_10 : retentionCheckB 1 .hat 10 = true :=
  retention_of_rejected 1 .hat 10 reject1A_10
theorem retention1A_11 : retentionCheckB 1 .hat 11 = true :=
  retention_of_rejected 1 .hat 11 reject1A_11
theorem retention1A_13 : retentionCheckB 1 .hat 13 = true :=
  retention_of_kept 1 .hat 13 (by rfl)
theorem retention1A_15 : retentionCheckB 1 .hat 15 = true :=
  retention_of_kept 1 .hat 15 (by rfl)
theorem retention1A_16 : retentionCheckB 1 .hat 16 = true :=
  retention_of_kept 1 .hat 16 (by rfl)
theorem retention1A_17 : retentionCheckB 1 .hat 17 = true :=
  retention_of_kept 1 .hat 17 (by rfl)
theorem retention1A_21 : retentionCheckB 1 .hat 21 = true :=
  retention_of_kept 1 .hat 21 (by rfl)
theorem retention1A_22 : retentionCheckB 1 .hat 22 = true :=
  retention_of_kept 1 .hat 22 (by rfl)
theorem retention1A_23 : retentionCheckB 1 .hat 23 = true :=
  retention_of_kept 1 .hat 23 (by rfl)
theorem retention1A_24 : retentionCheckB 1 .hat 24 = true :=
  retention_of_kept 1 .hat 24 (by rfl)
theorem retention1A_block0 : [0,1,2,3,6,8,10,11,13,15,16,17,21,22,23,24].all (retentionCheckB 1 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention1A_0, retention1A_1, retention1A_2, retention1A_3, retention1A_6, retention1A_8, retention1A_10, retention1A_11, retention1A_13, retention1A_15, retention1A_16, retention1A_17, retention1A_21, retention1A_22, retention1A_23, retention1A_24] <;> rfl
end SpectreClusters.StageA
