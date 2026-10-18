module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart10
public import SpectreClusters.StageAReject0APart11
public import SpectreClusters.StageAReject0APart12
public import SpectreClusters.StageAReject0APart13

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_64 : retentionCheckB 0 .hat 64 = true :=
  retention_of_rejected 0 .hat 64 reject0A_64
theorem retention0A_65 : retentionCheckB 0 .hat 65 = true :=
  retention_of_rejected 0 .hat 65 reject0A_65
theorem retention0A_66 : retentionCheckB 0 .hat 66 = true :=
  retention_of_rejected 0 .hat 66 reject0A_66
theorem retention0A_67 : retentionCheckB 0 .hat 67 = true :=
  retention_of_rejected 0 .hat 67 reject0A_67
theorem retention0A_68 : retentionCheckB 0 .hat 68 = true :=
  retention_of_rejected 0 .hat 68 reject0A_68
theorem retention0A_69 : retentionCheckB 0 .hat 69 = true :=
  retention_of_rejected 0 .hat 69 reject0A_69
theorem retention0A_70 : retentionCheckB 0 .hat 70 = true :=
  retention_of_rejected 0 .hat 70 reject0A_70
theorem retention0A_71 : retentionCheckB 0 .hat 71 = true :=
  retention_of_rejected 0 .hat 71 reject0A_71
theorem retention0A_72 : retentionCheckB 0 .hat 72 = true :=
  retention_of_rejected 0 .hat 72 reject0A_72
theorem retention0A_73 : retentionCheckB 0 .hat 73 = true :=
  retention_of_rejected 0 .hat 73 reject0A_73
theorem retention0A_74 : retentionCheckB 0 .hat 74 = true :=
  retention_of_rejected 0 .hat 74 reject0A_74
theorem retention0A_75 : retentionCheckB 0 .hat 75 = true :=
  retention_of_rejected 0 .hat 75 reject0A_75
theorem retention0A_76 : retentionCheckB 0 .hat 76 = true :=
  retention_of_rejected 0 .hat 76 reject0A_76
theorem retention0A_77 : retentionCheckB 0 .hat 77 = true :=
  retention_of_rejected 0 .hat 77 reject0A_77
theorem retention0A_78 : retentionCheckB 0 .hat 78 = true :=
  retention_of_rejected 0 .hat 78 reject0A_78
theorem retention0A_79 : retentionCheckB 0 .hat 79 = true :=
  retention_of_kept 0 .hat 79 (by rfl)
theorem retention0A_block4 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_64, retention0A_65, retention0A_66, retention0A_67, retention0A_68, retention0A_69, retention0A_70, retention0A_71, retention0A_72, retention0A_73, retention0A_74, retention0A_75, retention0A_76, retention0A_77, retention0A_78, retention0A_79] <;> rfl
end SpectreClusters.StageA
