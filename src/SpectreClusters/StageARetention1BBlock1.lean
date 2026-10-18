module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject1BPart1

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention1B_219 : retentionCheckB 1 .turtle 219 = true :=
  retention_of_kept 1 .turtle 219 (by rfl)
theorem retention1B_221 : retentionCheckB 1 .turtle 221 = true :=
  retention_of_kept 1 .turtle 221 (by rfl)
theorem retention1B_222 : retentionCheckB 1 .turtle 222 = true :=
  retention_of_kept 1 .turtle 222 (by rfl)
theorem retention1B_223 : retentionCheckB 1 .turtle 223 = true :=
  retention_of_kept 1 .turtle 223 (by rfl)
theorem retention1B_226 : retentionCheckB 1 .turtle 226 = true :=
  retention_of_kept 1 .turtle 226 (by rfl)
theorem retention1B_227 : retentionCheckB 1 .turtle 227 = true :=
  retention_of_kept 1 .turtle 227 (by rfl)
theorem retention1B_229 : retentionCheckB 1 .turtle 229 = true :=
  retention_of_kept 1 .turtle 229 (by rfl)
theorem retention1B_231 : retentionCheckB 1 .turtle 231 = true :=
  retention_of_kept 1 .turtle 231 (by rfl)
theorem retention1B_240 : retentionCheckB 1 .turtle 240 = true :=
  retention_of_kept 1 .turtle 240 (by rfl)
theorem retention1B_242 : retentionCheckB 1 .turtle 242 = true :=
  retention_of_kept 1 .turtle 242 (by rfl)
theorem retention1B_244 : retentionCheckB 1 .turtle 244 = true :=
  retention_of_rejected 1 .turtle 244 reject1B_244
theorem retention1B_246 : retentionCheckB 1 .turtle 246 = true :=
  retention_of_kept 1 .turtle 246 (by rfl)
theorem retention1B_248 : retentionCheckB 1 .turtle 248 = true :=
  retention_of_kept 1 .turtle 248 (by rfl)
theorem retention1B_250 : retentionCheckB 1 .turtle 250 = true :=
  retention_of_kept 1 .turtle 250 (by rfl)
theorem retention1B_block1 : [219,221,222,223,226,227,229,231,240,242,244,246,248,250].all (retentionCheckB 1 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention1B_219, retention1B_221, retention1B_222, retention1B_223, retention1B_226, retention1B_227, retention1B_229, retention1B_231, retention1B_240, retention1B_242, retention1B_244, retention1B_246, retention1B_248, retention1B_250] <;> rfl
end SpectreClusters.StageA
