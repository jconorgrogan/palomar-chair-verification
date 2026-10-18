module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart25
public import SpectreClusters.StageAReject0APart26
public import SpectreClusters.StageAReject0APart27
public import SpectreClusters.StageAReject0APart28

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_128 : retentionCheckB 0 .hat 128 = true :=
  retention_of_rejected 0 .hat 128 reject0A_128
theorem retention0A_129 : retentionCheckB 0 .hat 129 = true :=
  retention_of_rejected 0 .hat 129 reject0A_129
theorem retention0A_130 : retentionCheckB 0 .hat 130 = true :=
  retention_of_rejected 0 .hat 130 reject0A_130
theorem retention0A_131 : retentionCheckB 0 .hat 131 = true :=
  retention_of_rejected 0 .hat 131 reject0A_131
theorem retention0A_132 : retentionCheckB 0 .hat 132 = true :=
  retention_of_rejected 0 .hat 132 reject0A_132
theorem retention0A_133 : retentionCheckB 0 .hat 133 = true :=
  retention_of_rejected 0 .hat 133 reject0A_133
theorem retention0A_134 : retentionCheckB 0 .hat 134 = true :=
  retention_of_rejected 0 .hat 134 reject0A_134
theorem retention0A_135 : retentionCheckB 0 .hat 135 = true :=
  retention_of_rejected 0 .hat 135 reject0A_135
theorem retention0A_136 : retentionCheckB 0 .hat 136 = true :=
  retention_of_rejected 0 .hat 136 reject0A_136
theorem retention0A_137 : retentionCheckB 0 .hat 137 = true :=
  retention_of_rejected 0 .hat 137 reject0A_137
theorem retention0A_138 : retentionCheckB 0 .hat 138 = true :=
  retention_of_rejected 0 .hat 138 reject0A_138
theorem retention0A_139 : retentionCheckB 0 .hat 139 = true :=
  retention_of_rejected 0 .hat 139 reject0A_139
theorem retention0A_140 : retentionCheckB 0 .hat 140 = true :=
  retention_of_rejected 0 .hat 140 reject0A_140
theorem retention0A_141 : retentionCheckB 0 .hat 141 = true :=
  retention_of_rejected 0 .hat 141 reject0A_141
theorem retention0A_142 : retentionCheckB 0 .hat 142 = true :=
  retention_of_rejected 0 .hat 142 reject0A_142
theorem retention0A_143 : retentionCheckB 0 .hat 143 = true :=
  retention_of_rejected 0 .hat 143 reject0A_143
theorem retention0A_block8 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_128, retention0A_129, retention0A_130, retention0A_131, retention0A_132, retention0A_133, retention0A_134, retention0A_135, retention0A_136, retention0A_137, retention0A_138, retention0A_139, retention0A_140, retention0A_141, retention0A_142, retention0A_143] <;> rfl
end SpectreClusters.StageA
