module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart19
public import SpectreClusters.StageAReject0BPart20
public import SpectreClusters.StageAReject0BPart21
public import SpectreClusters.StageAReject0BPart22
public import SpectreClusters.StageAReject0BPart23

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_80 : retentionCheckB 0 .turtle 80 = true :=
  retention_of_rejected 0 .turtle 80 reject0B_80
theorem retention0B_81 : retentionCheckB 0 .turtle 81 = true :=
  retention_of_rejected 0 .turtle 81 reject0B_81
theorem retention0B_82 : retentionCheckB 0 .turtle 82 = true :=
  retention_of_rejected 0 .turtle 82 reject0B_82
theorem retention0B_83 : retentionCheckB 0 .turtle 83 = true :=
  retention_of_rejected 0 .turtle 83 reject0B_83
theorem retention0B_84 : retentionCheckB 0 .turtle 84 = true :=
  retention_of_rejected 0 .turtle 84 reject0B_84
theorem retention0B_85 : retentionCheckB 0 .turtle 85 = true :=
  retention_of_rejected 0 .turtle 85 reject0B_85
theorem retention0B_86 : retentionCheckB 0 .turtle 86 = true :=
  retention_of_rejected 0 .turtle 86 reject0B_86
theorem retention0B_87 : retentionCheckB 0 .turtle 87 = true :=
  retention_of_rejected 0 .turtle 87 reject0B_87
theorem retention0B_88 : retentionCheckB 0 .turtle 88 = true :=
  retention_of_rejected 0 .turtle 88 reject0B_88
theorem retention0B_89 : retentionCheckB 0 .turtle 89 = true :=
  retention_of_rejected 0 .turtle 89 reject0B_89
theorem retention0B_90 : retentionCheckB 0 .turtle 90 = true :=
  retention_of_rejected 0 .turtle 90 reject0B_90
theorem retention0B_91 : retentionCheckB 0 .turtle 91 = true :=
  retention_of_rejected 0 .turtle 91 reject0B_91
theorem retention0B_92 : retentionCheckB 0 .turtle 92 = true :=
  retention_of_rejected 0 .turtle 92 reject0B_92
theorem retention0B_93 : retentionCheckB 0 .turtle 93 = true :=
  retention_of_rejected 0 .turtle 93 reject0B_93
theorem retention0B_94 : retentionCheckB 0 .turtle 94 = true :=
  retention_of_rejected 0 .turtle 94 reject0B_94
theorem retention0B_95 : retentionCheckB 0 .turtle 95 = true :=
  retention_of_rejected 0 .turtle 95 reject0B_95
theorem retention0B_block5 : [80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_80, retention0B_81, retention0B_82, retention0B_83, retention0B_84, retention0B_85, retention0B_86, retention0B_87, retention0B_88, retention0B_89, retention0B_90, retention0B_91, retention0B_92, retention0B_93, retention0B_94, retention0B_95] <;> rfl
end SpectreClusters.StageA
