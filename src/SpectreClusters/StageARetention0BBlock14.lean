module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart51
public import SpectreClusters.StageAReject0BPart52
public import SpectreClusters.StageAReject0BPart53

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_224 : retentionCheckB 0 .turtle 224 = true :=
  retention_of_rejected 0 .turtle 224 reject0B_224
theorem retention0B_225 : retentionCheckB 0 .turtle 225 = true :=
  retention_of_rejected 0 .turtle 225 reject0B_225
theorem retention0B_226 : retentionCheckB 0 .turtle 226 = true :=
  retention_of_kept 0 .turtle 226 (by rfl)
theorem retention0B_227 : retentionCheckB 0 .turtle 227 = true :=
  retention_of_kept 0 .turtle 227 (by rfl)
theorem retention0B_228 : retentionCheckB 0 .turtle 228 = true :=
  retention_of_rejected 0 .turtle 228 reject0B_228
theorem retention0B_229 : retentionCheckB 0 .turtle 229 = true :=
  retention_of_kept 0 .turtle 229 (by rfl)
theorem retention0B_230 : retentionCheckB 0 .turtle 230 = true :=
  retention_of_rejected 0 .turtle 230 reject0B_230
theorem retention0B_231 : retentionCheckB 0 .turtle 231 = true :=
  retention_of_kept 0 .turtle 231 (by rfl)
theorem retention0B_232 : retentionCheckB 0 .turtle 232 = true :=
  retention_of_rejected 0 .turtle 232 reject0B_232
theorem retention0B_233 : retentionCheckB 0 .turtle 233 = true :=
  retention_of_rejected 0 .turtle 233 reject0B_233
theorem retention0B_234 : retentionCheckB 0 .turtle 234 = true :=
  retention_of_rejected 0 .turtle 234 reject0B_234
theorem retention0B_235 : retentionCheckB 0 .turtle 235 = true :=
  retention_of_rejected 0 .turtle 235 reject0B_235
theorem retention0B_236 : retentionCheckB 0 .turtle 236 = true :=
  retention_of_rejected 0 .turtle 236 reject0B_236
theorem retention0B_237 : retentionCheckB 0 .turtle 237 = true :=
  retention_of_rejected 0 .turtle 237 reject0B_237
theorem retention0B_238 : retentionCheckB 0 .turtle 238 = true :=
  retention_of_rejected 0 .turtle 238 reject0B_238
theorem retention0B_239 : retentionCheckB 0 .turtle 239 = true :=
  retention_of_rejected 0 .turtle 239 reject0B_239
theorem retention0B_block14 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_224, retention0B_225, retention0B_226, retention0B_227, retention0B_228, retention0B_229, retention0B_230, retention0B_231, retention0B_232, retention0B_233, retention0B_234, retention0B_235, retention0B_236, retention0B_237, retention0B_238, retention0B_239] <;> rfl
end SpectreClusters.StageA
