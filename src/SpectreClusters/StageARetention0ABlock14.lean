module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart48
public import SpectreClusters.StageAReject0APart49
public import SpectreClusters.StageAReject0APart50
public import SpectreClusters.StageAReject0APart51
public import SpectreClusters.StageAReject0APart52

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_224 : retentionCheckB 0 .hat 224 = true :=
  retention_of_rejected 0 .hat 224 reject0A_224
theorem retention0A_225 : retentionCheckB 0 .hat 225 = true :=
  retention_of_rejected 0 .hat 225 reject0A_225
theorem retention0A_226 : retentionCheckB 0 .hat 226 = true :=
  retention_of_rejected 0 .hat 226 reject0A_226
theorem retention0A_227 : retentionCheckB 0 .hat 227 = true :=
  retention_of_rejected 0 .hat 227 reject0A_227
theorem retention0A_228 : retentionCheckB 0 .hat 228 = true :=
  retention_of_rejected 0 .hat 228 reject0A_228
theorem retention0A_229 : retentionCheckB 0 .hat 229 = true :=
  retention_of_rejected 0 .hat 229 reject0A_229
theorem retention0A_230 : retentionCheckB 0 .hat 230 = true :=
  retention_of_rejected 0 .hat 230 reject0A_230
theorem retention0A_231 : retentionCheckB 0 .hat 231 = true :=
  retention_of_rejected 0 .hat 231 reject0A_231
theorem retention0A_232 : retentionCheckB 0 .hat 232 = true :=
  retention_of_rejected 0 .hat 232 reject0A_232
theorem retention0A_233 : retentionCheckB 0 .hat 233 = true :=
  retention_of_rejected 0 .hat 233 reject0A_233
theorem retention0A_234 : retentionCheckB 0 .hat 234 = true :=
  retention_of_rejected 0 .hat 234 reject0A_234
theorem retention0A_235 : retentionCheckB 0 .hat 235 = true :=
  retention_of_rejected 0 .hat 235 reject0A_235
theorem retention0A_236 : retentionCheckB 0 .hat 236 = true :=
  retention_of_rejected 0 .hat 236 reject0A_236
theorem retention0A_237 : retentionCheckB 0 .hat 237 = true :=
  retention_of_rejected 0 .hat 237 reject0A_237
theorem retention0A_238 : retentionCheckB 0 .hat 238 = true :=
  retention_of_rejected 0 .hat 238 reject0A_238
theorem retention0A_239 : retentionCheckB 0 .hat 239 = true :=
  retention_of_rejected 0 .hat 239 reject0A_239
theorem retention0A_block14 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_224, retention0A_225, retention0A_226, retention0A_227, retention0A_228, retention0A_229, retention0A_230, retention0A_231, retention0A_232, retention0A_233, retention0A_234, retention0A_235, retention0A_236, retention0A_237, retention0A_238, retention0A_239] <;> rfl
end SpectreClusters.StageA
