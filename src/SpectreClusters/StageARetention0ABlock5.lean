module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart13
public import SpectreClusters.StageAReject0APart14
public import SpectreClusters.StageAReject0APart15
public import SpectreClusters.StageAReject0APart16

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_80 : retentionCheckB 0 .hat 80 = true :=
  retention_of_rejected 0 .hat 80 reject0A_80
theorem retention0A_81 : retentionCheckB 0 .hat 81 = true :=
  retention_of_kept 0 .hat 81 (by rfl)
theorem retention0A_82 : retentionCheckB 0 .hat 82 = true :=
  retention_of_rejected 0 .hat 82 reject0A_82
theorem retention0A_83 : retentionCheckB 0 .hat 83 = true :=
  retention_of_rejected 0 .hat 83 reject0A_83
theorem retention0A_84 : retentionCheckB 0 .hat 84 = true :=
  retention_of_rejected 0 .hat 84 reject0A_84
theorem retention0A_85 : retentionCheckB 0 .hat 85 = true :=
  retention_of_rejected 0 .hat 85 reject0A_85
theorem retention0A_86 : retentionCheckB 0 .hat 86 = true :=
  retention_of_rejected 0 .hat 86 reject0A_86
theorem retention0A_87 : retentionCheckB 0 .hat 87 = true :=
  retention_of_rejected 0 .hat 87 reject0A_87
theorem retention0A_88 : retentionCheckB 0 .hat 88 = true :=
  retention_of_rejected 0 .hat 88 reject0A_88
theorem retention0A_89 : retentionCheckB 0 .hat 89 = true :=
  retention_of_kept 0 .hat 89 (by rfl)
theorem retention0A_90 : retentionCheckB 0 .hat 90 = true :=
  retention_of_rejected 0 .hat 90 reject0A_90
theorem retention0A_91 : retentionCheckB 0 .hat 91 = true :=
  retention_of_kept 0 .hat 91 (by rfl)
theorem retention0A_92 : retentionCheckB 0 .hat 92 = true :=
  retention_of_rejected 0 .hat 92 reject0A_92
theorem retention0A_93 : retentionCheckB 0 .hat 93 = true :=
  retention_of_rejected 0 .hat 93 reject0A_93
theorem retention0A_94 : retentionCheckB 0 .hat 94 = true :=
  retention_of_rejected 0 .hat 94 reject0A_94
theorem retention0A_95 : retentionCheckB 0 .hat 95 = true :=
  retention_of_rejected 0 .hat 95 reject0A_95
theorem retention0A_block5 : [80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_80, retention0A_81, retention0A_82, retention0A_83, retention0A_84, retention0A_85, retention0A_86, retention0A_87, retention0A_88, retention0A_89, retention0A_90, retention0A_91, retention0A_92, retention0A_93, retention0A_94, retention0A_95] <;> rfl
end SpectreClusters.StageA
