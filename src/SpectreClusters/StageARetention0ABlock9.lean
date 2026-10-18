module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart29
public import SpectreClusters.StageAReject0APart30
public import SpectreClusters.StageAReject0APart31
public import SpectreClusters.StageAReject0APart32

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_144 : retentionCheckB 0 .hat 144 = true :=
  retention_of_rejected 0 .hat 144 reject0A_144
theorem retention0A_145 : retentionCheckB 0 .hat 145 = true :=
  retention_of_rejected 0 .hat 145 reject0A_145
theorem retention0A_146 : retentionCheckB 0 .hat 146 = true :=
  retention_of_rejected 0 .hat 146 reject0A_146
theorem retention0A_147 : retentionCheckB 0 .hat 147 = true :=
  retention_of_rejected 0 .hat 147 reject0A_147
theorem retention0A_148 : retentionCheckB 0 .hat 148 = true :=
  retention_of_rejected 0 .hat 148 reject0A_148
theorem retention0A_149 : retentionCheckB 0 .hat 149 = true :=
  retention_of_rejected 0 .hat 149 reject0A_149
theorem retention0A_150 : retentionCheckB 0 .hat 150 = true :=
  retention_of_rejected 0 .hat 150 reject0A_150
theorem retention0A_151 : retentionCheckB 0 .hat 151 = true :=
  retention_of_rejected 0 .hat 151 reject0A_151
theorem retention0A_152 : retentionCheckB 0 .hat 152 = true :=
  retention_of_rejected 0 .hat 152 reject0A_152
theorem retention0A_153 : retentionCheckB 0 .hat 153 = true :=
  retention_of_rejected 0 .hat 153 reject0A_153
theorem retention0A_154 : retentionCheckB 0 .hat 154 = true :=
  retention_of_rejected 0 .hat 154 reject0A_154
theorem retention0A_155 : retentionCheckB 0 .hat 155 = true :=
  retention_of_rejected 0 .hat 155 reject0A_155
theorem retention0A_156 : retentionCheckB 0 .hat 156 = true :=
  retention_of_rejected 0 .hat 156 reject0A_156
theorem retention0A_157 : retentionCheckB 0 .hat 157 = true :=
  retention_of_rejected 0 .hat 157 reject0A_157
theorem retention0A_158 : retentionCheckB 0 .hat 158 = true :=
  retention_of_rejected 0 .hat 158 reject0A_158
theorem retention0A_159 : retentionCheckB 0 .hat 159 = true :=
  retention_of_rejected 0 .hat 159 reject0A_159
theorem retention0A_block9 : [144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_144, retention0A_145, retention0A_146, retention0A_147, retention0A_148, retention0A_149, retention0A_150, retention0A_151, retention0A_152, retention0A_153, retention0A_154, retention0A_155, retention0A_156, retention0A_157, retention0A_158, retention0A_159] <;> rfl
end SpectreClusters.StageA
