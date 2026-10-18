module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart3
public import SpectreClusters.StageAReject0APart4
public import SpectreClusters.StageAReject0APart5

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_32 : retentionCheckB 0 .hat 32 = true :=
  retention_of_kept 0 .hat 32 (by rfl)
theorem retention0A_33 : retentionCheckB 0 .hat 33 = true :=
  retention_of_rejected 0 .hat 33 reject0A_33
theorem retention0A_34 : retentionCheckB 0 .hat 34 = true :=
  retention_of_kept 0 .hat 34 (by rfl)
theorem retention0A_35 : retentionCheckB 0 .hat 35 = true :=
  retention_of_kept 0 .hat 35 (by rfl)
theorem retention0A_36 : retentionCheckB 0 .hat 36 = true :=
  retention_of_rejected 0 .hat 36 reject0A_36
theorem retention0A_37 : retentionCheckB 0 .hat 37 = true :=
  retention_of_rejected 0 .hat 37 reject0A_37
theorem retention0A_38 : retentionCheckB 0 .hat 38 = true :=
  retention_of_kept 0 .hat 38 (by rfl)
theorem retention0A_39 : retentionCheckB 0 .hat 39 = true :=
  retention_of_kept 0 .hat 39 (by rfl)
theorem retention0A_40 : retentionCheckB 0 .hat 40 = true :=
  retention_of_rejected 0 .hat 40 reject0A_40
theorem retention0A_41 : retentionCheckB 0 .hat 41 = true :=
  retention_of_rejected 0 .hat 41 reject0A_41
theorem retention0A_42 : retentionCheckB 0 .hat 42 = true :=
  retention_of_rejected 0 .hat 42 reject0A_42
theorem retention0A_43 : retentionCheckB 0 .hat 43 = true :=
  retention_of_rejected 0 .hat 43 reject0A_43
theorem retention0A_44 : retentionCheckB 0 .hat 44 = true :=
  retention_of_rejected 0 .hat 44 reject0A_44
theorem retention0A_45 : retentionCheckB 0 .hat 45 = true :=
  retention_of_rejected 0 .hat 45 reject0A_45
theorem retention0A_46 : retentionCheckB 0 .hat 46 = true :=
  retention_of_rejected 0 .hat 46 reject0A_46
theorem retention0A_47 : retentionCheckB 0 .hat 47 = true :=
  retention_of_rejected 0 .hat 47 reject0A_47
theorem retention0A_block2 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_32, retention0A_33, retention0A_34, retention0A_35, retention0A_36, retention0A_37, retention0A_38, retention0A_39, retention0A_40, retention0A_41, retention0A_42, retention0A_43, retention0A_44, retention0A_45, retention0A_46, retention0A_47] <;> rfl
end SpectreClusters.StageA
