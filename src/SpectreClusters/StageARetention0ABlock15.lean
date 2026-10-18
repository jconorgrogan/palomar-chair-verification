module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart52
public import SpectreClusters.StageAReject0APart53
public import SpectreClusters.StageAReject0APart54
public import SpectreClusters.StageAReject0APart55

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_240 : retentionCheckB 0 .hat 240 = true :=
  retention_of_rejected 0 .hat 240 reject0A_240
theorem retention0A_241 : retentionCheckB 0 .hat 241 = true :=
  retention_of_rejected 0 .hat 241 reject0A_241
theorem retention0A_242 : retentionCheckB 0 .hat 242 = true :=
  retention_of_rejected 0 .hat 242 reject0A_242
theorem retention0A_243 : retentionCheckB 0 .hat 243 = true :=
  retention_of_rejected 0 .hat 243 reject0A_243
theorem retention0A_244 : retentionCheckB 0 .hat 244 = true :=
  retention_of_rejected 0 .hat 244 reject0A_244
theorem retention0A_245 : retentionCheckB 0 .hat 245 = true :=
  retention_of_rejected 0 .hat 245 reject0A_245
theorem retention0A_246 : retentionCheckB 0 .hat 246 = true :=
  retention_of_kept 0 .hat 246 (by rfl)
theorem retention0A_247 : retentionCheckB 0 .hat 247 = true :=
  retention_of_rejected 0 .hat 247 reject0A_247
theorem retention0A_248 : retentionCheckB 0 .hat 248 = true :=
  retention_of_rejected 0 .hat 248 reject0A_248
theorem retention0A_249 : retentionCheckB 0 .hat 249 = true :=
  retention_of_rejected 0 .hat 249 reject0A_249
theorem retention0A_250 : retentionCheckB 0 .hat 250 = true :=
  retention_of_rejected 0 .hat 250 reject0A_250
theorem retention0A_block15 : [240,241,242,243,244,245,246,247,248,249,250].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_240, retention0A_241, retention0A_242, retention0A_243, retention0A_244, retention0A_245, retention0A_246, retention0A_247, retention0A_248, retention0A_249, retention0A_250] <;> rfl
end SpectreClusters.StageA
