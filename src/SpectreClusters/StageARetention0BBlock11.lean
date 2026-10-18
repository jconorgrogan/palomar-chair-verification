module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart43
public import SpectreClusters.StageAReject0BPart44
public import SpectreClusters.StageAReject0BPart45
public import SpectreClusters.StageAReject0BPart46

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_176 : retentionCheckB 0 .turtle 176 = true :=
  retention_of_rejected 0 .turtle 176 reject0B_176
theorem retention0B_177 : retentionCheckB 0 .turtle 177 = true :=
  retention_of_rejected 0 .turtle 177 reject0B_177
theorem retention0B_178 : retentionCheckB 0 .turtle 178 = true :=
  retention_of_rejected 0 .turtle 178 reject0B_178
theorem retention0B_179 : retentionCheckB 0 .turtle 179 = true :=
  retention_of_kept 0 .turtle 179 (by rfl)
theorem retention0B_180 : retentionCheckB 0 .turtle 180 = true :=
  retention_of_rejected 0 .turtle 180 reject0B_180
theorem retention0B_181 : retentionCheckB 0 .turtle 181 = true :=
  retention_of_rejected 0 .turtle 181 reject0B_181
theorem retention0B_182 : retentionCheckB 0 .turtle 182 = true :=
  retention_of_rejected 0 .turtle 182 reject0B_182
theorem retention0B_183 : retentionCheckB 0 .turtle 183 = true :=
  retention_of_kept 0 .turtle 183 (by rfl)
theorem retention0B_184 : retentionCheckB 0 .turtle 184 = true :=
  retention_of_rejected 0 .turtle 184 reject0B_184
theorem retention0B_185 : retentionCheckB 0 .turtle 185 = true :=
  retention_of_rejected 0 .turtle 185 reject0B_185
theorem retention0B_186 : retentionCheckB 0 .turtle 186 = true :=
  retention_of_rejected 0 .turtle 186 reject0B_186
theorem retention0B_187 : retentionCheckB 0 .turtle 187 = true :=
  retention_of_rejected 0 .turtle 187 reject0B_187
theorem retention0B_188 : retentionCheckB 0 .turtle 188 = true :=
  retention_of_rejected 0 .turtle 188 reject0B_188
theorem retention0B_189 : retentionCheckB 0 .turtle 189 = true :=
  retention_of_rejected 0 .turtle 189 reject0B_189
theorem retention0B_190 : retentionCheckB 0 .turtle 190 = true :=
  retention_of_rejected 0 .turtle 190 reject0B_190
theorem retention0B_191 : retentionCheckB 0 .turtle 191 = true :=
  retention_of_rejected 0 .turtle 191 reject0B_191
theorem retention0B_block11 : [176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_176, retention0B_177, retention0B_178, retention0B_179, retention0B_180, retention0B_181, retention0B_182, retention0B_183, retention0B_184, retention0B_185, retention0B_186, retention0B_187, retention0B_188, retention0B_189, retention0B_190, retention0B_191] <;> rfl
end SpectreClusters.StageA
