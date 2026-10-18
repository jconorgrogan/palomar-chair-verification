module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart54
public import SpectreClusters.StageAReject0BPart55

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_240 : retentionCheckB 0 .turtle 240 = true :=
  retention_of_kept 0 .turtle 240 (by rfl)
theorem retention0B_241 : retentionCheckB 0 .turtle 241 = true :=
  retention_of_rejected 0 .turtle 241 reject0B_241
theorem retention0B_242 : retentionCheckB 0 .turtle 242 = true :=
  retention_of_kept 0 .turtle 242 (by rfl)
theorem retention0B_243 : retentionCheckB 0 .turtle 243 = true :=
  retention_of_rejected 0 .turtle 243 reject0B_243
theorem retention0B_244 : retentionCheckB 0 .turtle 244 = true :=
  retention_of_kept 0 .turtle 244 (by rfl)
theorem retention0B_245 : retentionCheckB 0 .turtle 245 = true :=
  retention_of_rejected 0 .turtle 245 reject0B_245
theorem retention0B_246 : retentionCheckB 0 .turtle 246 = true :=
  retention_of_kept 0 .turtle 246 (by rfl)
theorem retention0B_247 : retentionCheckB 0 .turtle 247 = true :=
  retention_of_rejected 0 .turtle 247 reject0B_247
theorem retention0B_248 : retentionCheckB 0 .turtle 248 = true :=
  retention_of_kept 0 .turtle 248 (by rfl)
theorem retention0B_249 : retentionCheckB 0 .turtle 249 = true :=
  retention_of_rejected 0 .turtle 249 reject0B_249
theorem retention0B_250 : retentionCheckB 0 .turtle 250 = true :=
  retention_of_kept 0 .turtle 250 (by rfl)
theorem retention0B_block15 : [240,241,242,243,244,245,246,247,248,249,250].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_240, retention0B_241, retention0B_242, retention0B_243, retention0B_244, retention0B_245, retention0B_246, retention0B_247, retention0B_248, retention0B_249, retention0B_250] <;> rfl
end SpectreClusters.StageA
