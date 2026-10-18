module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart27
public import SpectreClusters.StageAReject0BPart28
public import SpectreClusters.StageAReject0BPart29
public import SpectreClusters.StageAReject0BPart30
public import SpectreClusters.StageAReject0BPart31

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_112 : retentionCheckB 0 .turtle 112 = true :=
  retention_of_rejected 0 .turtle 112 reject0B_112
theorem retention0B_113 : retentionCheckB 0 .turtle 113 = true :=
  retention_of_rejected 0 .turtle 113 reject0B_113
theorem retention0B_114 : retentionCheckB 0 .turtle 114 = true :=
  retention_of_rejected 0 .turtle 114 reject0B_114
theorem retention0B_115 : retentionCheckB 0 .turtle 115 = true :=
  retention_of_rejected 0 .turtle 115 reject0B_115
theorem retention0B_116 : retentionCheckB 0 .turtle 116 = true :=
  retention_of_rejected 0 .turtle 116 reject0B_116
theorem retention0B_117 : retentionCheckB 0 .turtle 117 = true :=
  retention_of_rejected 0 .turtle 117 reject0B_117
theorem retention0B_118 : retentionCheckB 0 .turtle 118 = true :=
  retention_of_rejected 0 .turtle 118 reject0B_118
theorem retention0B_119 : retentionCheckB 0 .turtle 119 = true :=
  retention_of_rejected 0 .turtle 119 reject0B_119
theorem retention0B_120 : retentionCheckB 0 .turtle 120 = true :=
  retention_of_rejected 0 .turtle 120 reject0B_120
theorem retention0B_121 : retentionCheckB 0 .turtle 121 = true :=
  retention_of_rejected 0 .turtle 121 reject0B_121
theorem retention0B_122 : retentionCheckB 0 .turtle 122 = true :=
  retention_of_rejected 0 .turtle 122 reject0B_122
theorem retention0B_123 : retentionCheckB 0 .turtle 123 = true :=
  retention_of_rejected 0 .turtle 123 reject0B_123
theorem retention0B_124 : retentionCheckB 0 .turtle 124 = true :=
  retention_of_rejected 0 .turtle 124 reject0B_124
theorem retention0B_125 : retentionCheckB 0 .turtle 125 = true :=
  retention_of_rejected 0 .turtle 125 reject0B_125
theorem retention0B_126 : retentionCheckB 0 .turtle 126 = true :=
  retention_of_rejected 0 .turtle 126 reject0B_126
theorem retention0B_127 : retentionCheckB 0 .turtle 127 = true :=
  retention_of_rejected 0 .turtle 127 reject0B_127
theorem retention0B_block7 : [112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_112, retention0B_113, retention0B_114, retention0B_115, retention0B_116, retention0B_117, retention0B_118, retention0B_119, retention0B_120, retention0B_121, retention0B_122, retention0B_123, retention0B_124, retention0B_125, retention0B_126, retention0B_127] <;> rfl
end SpectreClusters.StageA
