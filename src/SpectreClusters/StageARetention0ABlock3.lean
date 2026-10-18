module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart6
public import SpectreClusters.StageAReject0APart7
public import SpectreClusters.StageAReject0APart8
public import SpectreClusters.StageAReject0APart9

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_48 : retentionCheckB 0 .hat 48 = true :=
  retention_of_rejected 0 .hat 48 reject0A_48
theorem retention0A_49 : retentionCheckB 0 .hat 49 = true :=
  retention_of_rejected 0 .hat 49 reject0A_49
theorem retention0A_50 : retentionCheckB 0 .hat 50 = true :=
  retention_of_rejected 0 .hat 50 reject0A_50
theorem retention0A_51 : retentionCheckB 0 .hat 51 = true :=
  retention_of_rejected 0 .hat 51 reject0A_51
theorem retention0A_52 : retentionCheckB 0 .hat 52 = true :=
  retention_of_rejected 0 .hat 52 reject0A_52
theorem retention0A_53 : retentionCheckB 0 .hat 53 = true :=
  retention_of_rejected 0 .hat 53 reject0A_53
theorem retention0A_54 : retentionCheckB 0 .hat 54 = true :=
  retention_of_rejected 0 .hat 54 reject0A_54
theorem retention0A_55 : retentionCheckB 0 .hat 55 = true :=
  retention_of_rejected 0 .hat 55 reject0A_55
theorem retention0A_56 : retentionCheckB 0 .hat 56 = true :=
  retention_of_rejected 0 .hat 56 reject0A_56
theorem retention0A_57 : retentionCheckB 0 .hat 57 = true :=
  retention_of_rejected 0 .hat 57 reject0A_57
theorem retention0A_58 : retentionCheckB 0 .hat 58 = true :=
  retention_of_rejected 0 .hat 58 reject0A_58
theorem retention0A_59 : retentionCheckB 0 .hat 59 = true :=
  retention_of_rejected 0 .hat 59 reject0A_59
theorem retention0A_60 : retentionCheckB 0 .hat 60 = true :=
  retention_of_rejected 0 .hat 60 reject0A_60
theorem retention0A_61 : retentionCheckB 0 .hat 61 = true :=
  retention_of_rejected 0 .hat 61 reject0A_61
theorem retention0A_62 : retentionCheckB 0 .hat 62 = true :=
  retention_of_rejected 0 .hat 62 reject0A_62
theorem retention0A_63 : retentionCheckB 0 .hat 63 = true :=
  retention_of_rejected 0 .hat 63 reject0A_63
theorem retention0A_block3 : [48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_48, retention0A_49, retention0A_50, retention0A_51, retention0A_52, retention0A_53, retention0A_54, retention0A_55, retention0A_56, retention0A_57, retention0A_58, retention0A_59, retention0A_60, retention0A_61, retention0A_62, retention0A_63] <;> rfl
end SpectreClusters.StageA
