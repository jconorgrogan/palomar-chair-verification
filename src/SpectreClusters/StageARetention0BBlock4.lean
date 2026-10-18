module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart15
public import SpectreClusters.StageAReject0BPart16
public import SpectreClusters.StageAReject0BPart17
public import SpectreClusters.StageAReject0BPart18
public import SpectreClusters.StageAReject0BPart19

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_64 : retentionCheckB 0 .turtle 64 = true :=
  retention_of_rejected 0 .turtle 64 reject0B_64
theorem retention0B_65 : retentionCheckB 0 .turtle 65 = true :=
  retention_of_rejected 0 .turtle 65 reject0B_65
theorem retention0B_66 : retentionCheckB 0 .turtle 66 = true :=
  retention_of_rejected 0 .turtle 66 reject0B_66
theorem retention0B_67 : retentionCheckB 0 .turtle 67 = true :=
  retention_of_rejected 0 .turtle 67 reject0B_67
theorem retention0B_68 : retentionCheckB 0 .turtle 68 = true :=
  retention_of_rejected 0 .turtle 68 reject0B_68
theorem retention0B_69 : retentionCheckB 0 .turtle 69 = true :=
  retention_of_rejected 0 .turtle 69 reject0B_69
theorem retention0B_70 : retentionCheckB 0 .turtle 70 = true :=
  retention_of_rejected 0 .turtle 70 reject0B_70
theorem retention0B_71 : retentionCheckB 0 .turtle 71 = true :=
  retention_of_rejected 0 .turtle 71 reject0B_71
theorem retention0B_72 : retentionCheckB 0 .turtle 72 = true :=
  retention_of_rejected 0 .turtle 72 reject0B_72
theorem retention0B_73 : retentionCheckB 0 .turtle 73 = true :=
  retention_of_rejected 0 .turtle 73 reject0B_73
theorem retention0B_74 : retentionCheckB 0 .turtle 74 = true :=
  retention_of_rejected 0 .turtle 74 reject0B_74
theorem retention0B_75 : retentionCheckB 0 .turtle 75 = true :=
  retention_of_rejected 0 .turtle 75 reject0B_75
theorem retention0B_76 : retentionCheckB 0 .turtle 76 = true :=
  retention_of_rejected 0 .turtle 76 reject0B_76
theorem retention0B_77 : retentionCheckB 0 .turtle 77 = true :=
  retention_of_rejected 0 .turtle 77 reject0B_77
theorem retention0B_78 : retentionCheckB 0 .turtle 78 = true :=
  retention_of_rejected 0 .turtle 78 reject0B_78
theorem retention0B_79 : retentionCheckB 0 .turtle 79 = true :=
  retention_of_rejected 0 .turtle 79 reject0B_79
theorem retention0B_block4 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_64, retention0B_65, retention0B_66, retention0B_67, retention0B_68, retention0B_69, retention0B_70, retention0B_71, retention0B_72, retention0B_73, retention0B_74, retention0B_75, retention0B_76, retention0B_77, retention0B_78, retention0B_79] <;> rfl
end SpectreClusters.StageA
