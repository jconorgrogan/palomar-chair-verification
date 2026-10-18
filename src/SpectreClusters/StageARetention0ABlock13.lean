module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart45
public import SpectreClusters.StageAReject0APart46
public import SpectreClusters.StageAReject0APart47
public import SpectreClusters.StageAReject0APart48

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_208 : retentionCheckB 0 .hat 208 = true :=
  retention_of_rejected 0 .hat 208 reject0A_208
theorem retention0A_209 : retentionCheckB 0 .hat 209 = true :=
  retention_of_rejected 0 .hat 209 reject0A_209
theorem retention0A_210 : retentionCheckB 0 .hat 210 = true :=
  retention_of_kept 0 .hat 210 (by rfl)
theorem retention0A_211 : retentionCheckB 0 .hat 211 = true :=
  retention_of_rejected 0 .hat 211 reject0A_211
theorem retention0A_212 : retentionCheckB 0 .hat 212 = true :=
  retention_of_rejected 0 .hat 212 reject0A_212
theorem retention0A_213 : retentionCheckB 0 .hat 213 = true :=
  retention_of_rejected 0 .hat 213 reject0A_213
theorem retention0A_214 : retentionCheckB 0 .hat 214 = true :=
  retention_of_rejected 0 .hat 214 reject0A_214
theorem retention0A_215 : retentionCheckB 0 .hat 215 = true :=
  retention_of_rejected 0 .hat 215 reject0A_215
theorem retention0A_216 : retentionCheckB 0 .hat 216 = true :=
  retention_of_rejected 0 .hat 216 reject0A_216
theorem retention0A_217 : retentionCheckB 0 .hat 217 = true :=
  retention_of_rejected 0 .hat 217 reject0A_217
theorem retention0A_218 : retentionCheckB 0 .hat 218 = true :=
  retention_of_rejected 0 .hat 218 reject0A_218
theorem retention0A_219 : retentionCheckB 0 .hat 219 = true :=
  retention_of_rejected 0 .hat 219 reject0A_219
theorem retention0A_220 : retentionCheckB 0 .hat 220 = true :=
  retention_of_rejected 0 .hat 220 reject0A_220
theorem retention0A_221 : retentionCheckB 0 .hat 221 = true :=
  retention_of_rejected 0 .hat 221 reject0A_221
theorem retention0A_222 : retentionCheckB 0 .hat 222 = true :=
  retention_of_rejected 0 .hat 222 reject0A_222
theorem retention0A_223 : retentionCheckB 0 .hat 223 = true :=
  retention_of_rejected 0 .hat 223 reject0A_223
theorem retention0A_block13 : [208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_208, retention0A_209, retention0A_210, retention0A_211, retention0A_212, retention0A_213, retention0A_214, retention0A_215, retention0A_216, retention0A_217, retention0A_218, retention0A_219, retention0A_220, retention0A_221, retention0A_222, retention0A_223] <;> rfl
end SpectreClusters.StageA
