module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart46
public import SpectreClusters.StageAReject0BPart47
public import SpectreClusters.StageAReject0BPart48
public import SpectreClusters.StageAReject0BPart49

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_192 : retentionCheckB 0 .turtle 192 = true :=
  retention_of_rejected 0 .turtle 192 reject0B_192
theorem retention0B_193 : retentionCheckB 0 .turtle 193 = true :=
  retention_of_rejected 0 .turtle 193 reject0B_193
theorem retention0B_194 : retentionCheckB 0 .turtle 194 = true :=
  retention_of_rejected 0 .turtle 194 reject0B_194
theorem retention0B_195 : retentionCheckB 0 .turtle 195 = true :=
  retention_of_rejected 0 .turtle 195 reject0B_195
theorem retention0B_196 : retentionCheckB 0 .turtle 196 = true :=
  retention_of_rejected 0 .turtle 196 reject0B_196
theorem retention0B_197 : retentionCheckB 0 .turtle 197 = true :=
  retention_of_rejected 0 .turtle 197 reject0B_197
theorem retention0B_198 : retentionCheckB 0 .turtle 198 = true :=
  retention_of_rejected 0 .turtle 198 reject0B_198
theorem retention0B_199 : retentionCheckB 0 .turtle 199 = true :=
  retention_of_rejected 0 .turtle 199 reject0B_199
theorem retention0B_200 : retentionCheckB 0 .turtle 200 = true :=
  retention_of_rejected 0 .turtle 200 reject0B_200
theorem retention0B_201 : retentionCheckB 0 .turtle 201 = true :=
  retention_of_kept 0 .turtle 201 (by rfl)
theorem retention0B_202 : retentionCheckB 0 .turtle 202 = true :=
  retention_of_rejected 0 .turtle 202 reject0B_202
theorem retention0B_203 : retentionCheckB 0 .turtle 203 = true :=
  retention_of_kept 0 .turtle 203 (by rfl)
theorem retention0B_204 : retentionCheckB 0 .turtle 204 = true :=
  retention_of_rejected 0 .turtle 204 reject0B_204
theorem retention0B_205 : retentionCheckB 0 .turtle 205 = true :=
  retention_of_kept 0 .turtle 205 (by rfl)
theorem retention0B_206 : retentionCheckB 0 .turtle 206 = true :=
  retention_of_kept 0 .turtle 206 (by rfl)
theorem retention0B_207 : retentionCheckB 0 .turtle 207 = true :=
  retention_of_kept 0 .turtle 207 (by rfl)
theorem retention0B_block12 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_192, retention0B_193, retention0B_194, retention0B_195, retention0B_196, retention0B_197, retention0B_198, retention0B_199, retention0B_200, retention0B_201, retention0B_202, retention0B_203, retention0B_204, retention0B_205, retention0B_206, retention0B_207] <;> rfl
end SpectreClusters.StageA
