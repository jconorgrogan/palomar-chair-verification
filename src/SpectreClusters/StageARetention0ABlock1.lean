module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart1
public import SpectreClusters.StageAReject0APart2
public import SpectreClusters.StageAReject0APart3

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_16 : retentionCheckB 0 .hat 16 = true :=
  retention_of_kept 0 .hat 16 (by rfl)
theorem retention0A_17 : retentionCheckB 0 .hat 17 = true :=
  retention_of_kept 0 .hat 17 (by rfl)
theorem retention0A_18 : retentionCheckB 0 .hat 18 = true :=
  retention_of_rejected 0 .hat 18 reject0A_18
theorem retention0A_19 : retentionCheckB 0 .hat 19 = true :=
  retention_of_rejected 0 .hat 19 reject0A_19
theorem retention0A_20 : retentionCheckB 0 .hat 20 = true :=
  retention_of_rejected 0 .hat 20 reject0A_20
theorem retention0A_21 : retentionCheckB 0 .hat 21 = true :=
  retention_of_kept 0 .hat 21 (by rfl)
theorem retention0A_22 : retentionCheckB 0 .hat 22 = true :=
  retention_of_kept 0 .hat 22 (by rfl)
theorem retention0A_23 : retentionCheckB 0 .hat 23 = true :=
  retention_of_kept 0 .hat 23 (by rfl)
theorem retention0A_24 : retentionCheckB 0 .hat 24 = true :=
  retention_of_kept 0 .hat 24 (by rfl)
theorem retention0A_25 : retentionCheckB 0 .hat 25 = true :=
  retention_of_rejected 0 .hat 25 reject0A_25
theorem retention0A_26 : retentionCheckB 0 .hat 26 = true :=
  retention_of_rejected 0 .hat 26 reject0A_26
theorem retention0A_27 : retentionCheckB 0 .hat 27 = true :=
  retention_of_kept 0 .hat 27 (by rfl)
theorem retention0A_28 : retentionCheckB 0 .hat 28 = true :=
  retention_of_kept 0 .hat 28 (by rfl)
theorem retention0A_29 : retentionCheckB 0 .hat 29 = true :=
  retention_of_rejected 0 .hat 29 reject0A_29
theorem retention0A_30 : retentionCheckB 0 .hat 30 = true :=
  retention_of_rejected 0 .hat 30 reject0A_30
theorem retention0A_31 : retentionCheckB 0 .hat 31 = true :=
  retention_of_kept 0 .hat 31 (by rfl)
theorem retention0A_block1 : [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_16, retention0A_17, retention0A_18, retention0A_19, retention0A_20, retention0A_21, retention0A_22, retention0A_23, retention0A_24, retention0A_25, retention0A_26, retention0A_27, retention0A_28, retention0A_29, retention0A_30, retention0A_31] <;> rfl
end SpectreClusters.StageA
