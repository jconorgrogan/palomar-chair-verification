module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart49
public import SpectreClusters.StageAReject0BPart50

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_208 : retentionCheckB 0 .turtle 208 = true :=
  retention_of_kept 0 .turtle 208 (by rfl)
theorem retention0B_209 : retentionCheckB 0 .turtle 209 = true :=
  retention_of_rejected 0 .turtle 209 reject0B_209
theorem retention0B_210 : retentionCheckB 0 .turtle 210 = true :=
  retention_of_rejected 0 .turtle 210 reject0B_210
theorem retention0B_211 : retentionCheckB 0 .turtle 211 = true :=
  retention_of_rejected 0 .turtle 211 reject0B_211
theorem retention0B_212 : retentionCheckB 0 .turtle 212 = true :=
  retention_of_kept 0 .turtle 212 (by rfl)
theorem retention0B_213 : retentionCheckB 0 .turtle 213 = true :=
  retention_of_rejected 0 .turtle 213 reject0B_213
theorem retention0B_214 : retentionCheckB 0 .turtle 214 = true :=
  retention_of_kept 0 .turtle 214 (by rfl)
theorem retention0B_215 : retentionCheckB 0 .turtle 215 = true :=
  retention_of_kept 0 .turtle 215 (by rfl)
theorem retention0B_216 : retentionCheckB 0 .turtle 216 = true :=
  retention_of_kept 0 .turtle 216 (by rfl)
theorem retention0B_217 : retentionCheckB 0 .turtle 217 = true :=
  retention_of_rejected 0 .turtle 217 reject0B_217
theorem retention0B_218 : retentionCheckB 0 .turtle 218 = true :=
  retention_of_rejected 0 .turtle 218 reject0B_218
theorem retention0B_219 : retentionCheckB 0 .turtle 219 = true :=
  retention_of_kept 0 .turtle 219 (by rfl)
theorem retention0B_220 : retentionCheckB 0 .turtle 220 = true :=
  retention_of_rejected 0 .turtle 220 reject0B_220
theorem retention0B_221 : retentionCheckB 0 .turtle 221 = true :=
  retention_of_kept 0 .turtle 221 (by rfl)
theorem retention0B_222 : retentionCheckB 0 .turtle 222 = true :=
  retention_of_kept 0 .turtle 222 (by rfl)
theorem retention0B_223 : retentionCheckB 0 .turtle 223 = true :=
  retention_of_kept 0 .turtle 223 (by rfl)
theorem retention0B_block13 : [208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_208, retention0B_209, retention0B_210, retention0B_211, retention0B_212, retention0B_213, retention0B_214, retention0B_215, retention0B_216, retention0B_217, retention0B_218, retention0B_219, retention0B_220, retention0B_221, retention0B_222, retention0B_223] <;> rfl
end SpectreClusters.StageA
