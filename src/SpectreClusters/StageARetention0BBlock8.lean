module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart31
public import SpectreClusters.StageAReject0BPart32
public import SpectreClusters.StageAReject0BPart33
public import SpectreClusters.StageAReject0BPart34
public import SpectreClusters.StageAReject0BPart35

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_128 : retentionCheckB 0 .turtle 128 = true :=
  retention_of_rejected 0 .turtle 128 reject0B_128
theorem retention0B_129 : retentionCheckB 0 .turtle 129 = true :=
  retention_of_rejected 0 .turtle 129 reject0B_129
theorem retention0B_130 : retentionCheckB 0 .turtle 130 = true :=
  retention_of_rejected 0 .turtle 130 reject0B_130
theorem retention0B_131 : retentionCheckB 0 .turtle 131 = true :=
  retention_of_rejected 0 .turtle 131 reject0B_131
theorem retention0B_132 : retentionCheckB 0 .turtle 132 = true :=
  retention_of_rejected 0 .turtle 132 reject0B_132
theorem retention0B_133 : retentionCheckB 0 .turtle 133 = true :=
  retention_of_rejected 0 .turtle 133 reject0B_133
theorem retention0B_134 : retentionCheckB 0 .turtle 134 = true :=
  retention_of_rejected 0 .turtle 134 reject0B_134
theorem retention0B_135 : retentionCheckB 0 .turtle 135 = true :=
  retention_of_rejected 0 .turtle 135 reject0B_135
theorem retention0B_136 : retentionCheckB 0 .turtle 136 = true :=
  retention_of_rejected 0 .turtle 136 reject0B_136
theorem retention0B_137 : retentionCheckB 0 .turtle 137 = true :=
  retention_of_rejected 0 .turtle 137 reject0B_137
theorem retention0B_138 : retentionCheckB 0 .turtle 138 = true :=
  retention_of_rejected 0 .turtle 138 reject0B_138
theorem retention0B_139 : retentionCheckB 0 .turtle 139 = true :=
  retention_of_rejected 0 .turtle 139 reject0B_139
theorem retention0B_140 : retentionCheckB 0 .turtle 140 = true :=
  retention_of_rejected 0 .turtle 140 reject0B_140
theorem retention0B_141 : retentionCheckB 0 .turtle 141 = true :=
  retention_of_rejected 0 .turtle 141 reject0B_141
theorem retention0B_142 : retentionCheckB 0 .turtle 142 = true :=
  retention_of_rejected 0 .turtle 142 reject0B_142
theorem retention0B_143 : retentionCheckB 0 .turtle 143 = true :=
  retention_of_rejected 0 .turtle 143 reject0B_143
theorem retention0B_block8 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_128, retention0B_129, retention0B_130, retention0B_131, retention0B_132, retention0B_133, retention0B_134, retention0B_135, retention0B_136, retention0B_137, retention0B_138, retention0B_139, retention0B_140, retention0B_141, retention0B_142, retention0B_143] <;> rfl
end SpectreClusters.StageA
