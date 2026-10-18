module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject1BPart0
public import SpectreClusters.StageAReject1BPart1

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention1B_0 : retentionCheckB 1 .turtle 0 = true :=
  retention_of_kept 1 .turtle 0 (by rfl)
theorem retention1B_52 : retentionCheckB 1 .turtle 52 = true :=
  retention_of_rejected 1 .turtle 52 reject1B_52
theorem retention1B_163 : retentionCheckB 1 .turtle 163 = true :=
  retention_of_kept 1 .turtle 163 (by rfl)
theorem retention1B_171 : retentionCheckB 1 .turtle 171 = true :=
  retention_of_kept 1 .turtle 171 (by rfl)
theorem retention1B_179 : retentionCheckB 1 .turtle 179 = true :=
  retention_of_kept 1 .turtle 179 (by rfl)
theorem retention1B_183 : retentionCheckB 1 .turtle 183 = true :=
  retention_of_rejected 1 .turtle 183 reject1B_183
theorem retention1B_201 : retentionCheckB 1 .turtle 201 = true :=
  retention_of_kept 1 .turtle 201 (by rfl)
theorem retention1B_203 : retentionCheckB 1 .turtle 203 = true :=
  retention_of_kept 1 .turtle 203 (by rfl)
theorem retention1B_205 : retentionCheckB 1 .turtle 205 = true :=
  retention_of_kept 1 .turtle 205 (by rfl)
theorem retention1B_206 : retentionCheckB 1 .turtle 206 = true :=
  retention_of_rejected 1 .turtle 206 reject1B_206
theorem retention1B_207 : retentionCheckB 1 .turtle 207 = true :=
  retention_of_rejected 1 .turtle 207 reject1B_207
theorem retention1B_208 : retentionCheckB 1 .turtle 208 = true :=
  retention_of_rejected 1 .turtle 208 reject1B_208
theorem retention1B_212 : retentionCheckB 1 .turtle 212 = true :=
  retention_of_kept 1 .turtle 212 (by rfl)
theorem retention1B_214 : retentionCheckB 1 .turtle 214 = true :=
  retention_of_kept 1 .turtle 214 (by rfl)
theorem retention1B_215 : retentionCheckB 1 .turtle 215 = true :=
  retention_of_kept 1 .turtle 215 (by rfl)
theorem retention1B_216 : retentionCheckB 1 .turtle 216 = true :=
  retention_of_rejected 1 .turtle 216 reject1B_216
theorem retention1B_block0 : [0,52,163,171,179,183,201,203,205,206,207,208,212,214,215,216].all (retentionCheckB 1 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention1B_0, retention1B_52, retention1B_163, retention1B_171, retention1B_179, retention1B_183, retention1B_201, retention1B_203, retention1B_205, retention1B_206, retention1B_207, retention1B_208, retention1B_212, retention1B_214, retention1B_215, retention1B_216] <;> rfl
end SpectreClusters.StageA
