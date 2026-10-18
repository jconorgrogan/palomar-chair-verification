module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart37
public import SpectreClusters.StageAReject0APart38
public import SpectreClusters.StageAReject0APart39
public import SpectreClusters.StageAReject0APart40

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_176 : retentionCheckB 0 .hat 176 = true :=
  retention_of_rejected 0 .hat 176 reject0A_176
theorem retention0A_177 : retentionCheckB 0 .hat 177 = true :=
  retention_of_rejected 0 .hat 177 reject0A_177
theorem retention0A_178 : retentionCheckB 0 .hat 178 = true :=
  retention_of_rejected 0 .hat 178 reject0A_178
theorem retention0A_179 : retentionCheckB 0 .hat 179 = true :=
  retention_of_rejected 0 .hat 179 reject0A_179
theorem retention0A_180 : retentionCheckB 0 .hat 180 = true :=
  retention_of_rejected 0 .hat 180 reject0A_180
theorem retention0A_181 : retentionCheckB 0 .hat 181 = true :=
  retention_of_rejected 0 .hat 181 reject0A_181
theorem retention0A_182 : retentionCheckB 0 .hat 182 = true :=
  retention_of_rejected 0 .hat 182 reject0A_182
theorem retention0A_183 : retentionCheckB 0 .hat 183 = true :=
  retention_of_rejected 0 .hat 183 reject0A_183
theorem retention0A_184 : retentionCheckB 0 .hat 184 = true :=
  retention_of_rejected 0 .hat 184 reject0A_184
theorem retention0A_185 : retentionCheckB 0 .hat 185 = true :=
  retention_of_rejected 0 .hat 185 reject0A_185
theorem retention0A_186 : retentionCheckB 0 .hat 186 = true :=
  retention_of_rejected 0 .hat 186 reject0A_186
theorem retention0A_187 : retentionCheckB 0 .hat 187 = true :=
  retention_of_rejected 0 .hat 187 reject0A_187
theorem retention0A_188 : retentionCheckB 0 .hat 188 = true :=
  retention_of_rejected 0 .hat 188 reject0A_188
theorem retention0A_189 : retentionCheckB 0 .hat 189 = true :=
  retention_of_rejected 0 .hat 189 reject0A_189
theorem retention0A_190 : retentionCheckB 0 .hat 190 = true :=
  retention_of_rejected 0 .hat 190 reject0A_190
theorem retention0A_191 : retentionCheckB 0 .hat 191 = true :=
  retention_of_rejected 0 .hat 191 reject0A_191
theorem retention0A_block11 : [176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_176, retention0A_177, retention0A_178, retention0A_179, retention0A_180, retention0A_181, retention0A_182, retention0A_183, retention0A_184, retention0A_185, retention0A_186, retention0A_187, retention0A_188, retention0A_189, retention0A_190, retention0A_191] <;> rfl
end SpectreClusters.StageA
