module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart41
public import SpectreClusters.StageAReject0APart42
public import SpectreClusters.StageAReject0APart43
public import SpectreClusters.StageAReject0APart44

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_192 : retentionCheckB 0 .hat 192 = true :=
  retention_of_rejected 0 .hat 192 reject0A_192
theorem retention0A_193 : retentionCheckB 0 .hat 193 = true :=
  retention_of_rejected 0 .hat 193 reject0A_193
theorem retention0A_194 : retentionCheckB 0 .hat 194 = true :=
  retention_of_rejected 0 .hat 194 reject0A_194
theorem retention0A_195 : retentionCheckB 0 .hat 195 = true :=
  retention_of_rejected 0 .hat 195 reject0A_195
theorem retention0A_196 : retentionCheckB 0 .hat 196 = true :=
  retention_of_rejected 0 .hat 196 reject0A_196
theorem retention0A_197 : retentionCheckB 0 .hat 197 = true :=
  retention_of_rejected 0 .hat 197 reject0A_197
theorem retention0A_198 : retentionCheckB 0 .hat 198 = true :=
  retention_of_rejected 0 .hat 198 reject0A_198
theorem retention0A_199 : retentionCheckB 0 .hat 199 = true :=
  retention_of_rejected 0 .hat 199 reject0A_199
theorem retention0A_200 : retentionCheckB 0 .hat 200 = true :=
  retention_of_rejected 0 .hat 200 reject0A_200
theorem retention0A_201 : retentionCheckB 0 .hat 201 = true :=
  retention_of_rejected 0 .hat 201 reject0A_201
theorem retention0A_202 : retentionCheckB 0 .hat 202 = true :=
  retention_of_rejected 0 .hat 202 reject0A_202
theorem retention0A_203 : retentionCheckB 0 .hat 203 = true :=
  retention_of_rejected 0 .hat 203 reject0A_203
theorem retention0A_204 : retentionCheckB 0 .hat 204 = true :=
  retention_of_rejected 0 .hat 204 reject0A_204
theorem retention0A_205 : retentionCheckB 0 .hat 205 = true :=
  retention_of_rejected 0 .hat 205 reject0A_205
theorem retention0A_206 : retentionCheckB 0 .hat 206 = true :=
  retention_of_rejected 0 .hat 206 reject0A_206
theorem retention0A_207 : retentionCheckB 0 .hat 207 = true :=
  retention_of_rejected 0 .hat 207 reject0A_207
theorem retention0A_block12 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_192, retention0A_193, retention0A_194, retention0A_195, retention0A_196, retention0A_197, retention0A_198, retention0A_199, retention0A_200, retention0A_201, retention0A_202, retention0A_203, retention0A_204, retention0A_205, retention0A_206, retention0A_207] <;> rfl
end SpectreClusters.StageA
