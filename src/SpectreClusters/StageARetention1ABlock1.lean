module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject1APart1

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention1A_27 : retentionCheckB 1 .hat 27 = true :=
  retention_of_kept 1 .hat 27 (by rfl)
theorem retention1A_28 : retentionCheckB 1 .hat 28 = true :=
  retention_of_kept 1 .hat 28 (by rfl)
theorem retention1A_31 : retentionCheckB 1 .hat 31 = true :=
  retention_of_kept 1 .hat 31 (by rfl)
theorem retention1A_32 : retentionCheckB 1 .hat 32 = true :=
  retention_of_kept 1 .hat 32 (by rfl)
theorem retention1A_34 : retentionCheckB 1 .hat 34 = true :=
  retention_of_rejected 1 .hat 34 reject1A_34
theorem retention1A_35 : retentionCheckB 1 .hat 35 = true :=
  retention_of_kept 1 .hat 35 (by rfl)
theorem retention1A_38 : retentionCheckB 1 .hat 38 = true :=
  retention_of_kept 1 .hat 38 (by rfl)
theorem retention1A_39 : retentionCheckB 1 .hat 39 = true :=
  retention_of_kept 1 .hat 39 (by rfl)
theorem retention1A_79 : retentionCheckB 1 .hat 79 = true :=
  retention_of_kept 1 .hat 79 (by rfl)
theorem retention1A_81 : retentionCheckB 1 .hat 81 = true :=
  retention_of_kept 1 .hat 81 (by rfl)
theorem retention1A_89 : retentionCheckB 1 .hat 89 = true :=
  retention_of_kept 1 .hat 89 (by rfl)
theorem retention1A_91 : retentionCheckB 1 .hat 91 = true :=
  retention_of_rejected 1 .hat 91 reject1A_91
theorem retention1A_210 : retentionCheckB 1 .hat 210 = true :=
  retention_of_kept 1 .hat 210 (by rfl)
theorem retention1A_246 : retentionCheckB 1 .hat 246 = true :=
  retention_of_rejected 1 .hat 246 reject1A_246
theorem retention1A_block1 : [27,28,31,32,34,35,38,39,79,81,89,91,210,246].all (retentionCheckB 1 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention1A_27, retention1A_28, retention1A_31, retention1A_32, retention1A_34, retention1A_35, retention1A_38, retention1A_39, retention1A_79, retention1A_81, retention1A_89, retention1A_91, retention1A_210, retention1A_246] <;> rfl
end SpectreClusters.StageA
