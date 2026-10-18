module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart39
public import SpectreClusters.StageAReject0BPart40
public import SpectreClusters.StageAReject0BPart41
public import SpectreClusters.StageAReject0BPart42

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_160 : retentionCheckB 0 .turtle 160 = true :=
  retention_of_rejected 0 .turtle 160 reject0B_160
theorem retention0B_161 : retentionCheckB 0 .turtle 161 = true :=
  retention_of_rejected 0 .turtle 161 reject0B_161
theorem retention0B_162 : retentionCheckB 0 .turtle 162 = true :=
  retention_of_rejected 0 .turtle 162 reject0B_162
theorem retention0B_163 : retentionCheckB 0 .turtle 163 = true :=
  retention_of_kept 0 .turtle 163 (by rfl)
theorem retention0B_164 : retentionCheckB 0 .turtle 164 = true :=
  retention_of_rejected 0 .turtle 164 reject0B_164
theorem retention0B_165 : retentionCheckB 0 .turtle 165 = true :=
  retention_of_rejected 0 .turtle 165 reject0B_165
theorem retention0B_166 : retentionCheckB 0 .turtle 166 = true :=
  retention_of_rejected 0 .turtle 166 reject0B_166
theorem retention0B_167 : retentionCheckB 0 .turtle 167 = true :=
  retention_of_rejected 0 .turtle 167 reject0B_167
theorem retention0B_168 : retentionCheckB 0 .turtle 168 = true :=
  retention_of_rejected 0 .turtle 168 reject0B_168
theorem retention0B_169 : retentionCheckB 0 .turtle 169 = true :=
  retention_of_rejected 0 .turtle 169 reject0B_169
theorem retention0B_170 : retentionCheckB 0 .turtle 170 = true :=
  retention_of_rejected 0 .turtle 170 reject0B_170
theorem retention0B_171 : retentionCheckB 0 .turtle 171 = true :=
  retention_of_kept 0 .turtle 171 (by rfl)
theorem retention0B_172 : retentionCheckB 0 .turtle 172 = true :=
  retention_of_rejected 0 .turtle 172 reject0B_172
theorem retention0B_173 : retentionCheckB 0 .turtle 173 = true :=
  retention_of_rejected 0 .turtle 173 reject0B_173
theorem retention0B_174 : retentionCheckB 0 .turtle 174 = true :=
  retention_of_rejected 0 .turtle 174 reject0B_174
theorem retention0B_175 : retentionCheckB 0 .turtle 175 = true :=
  retention_of_rejected 0 .turtle 175 reject0B_175
theorem retention0B_block10 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_160, retention0B_161, retention0B_162, retention0B_163, retention0B_164, retention0B_165, retention0B_166, retention0B_167, retention0B_168, retention0B_169, retention0B_170, retention0B_171, retention0B_172, retention0B_173, retention0B_174, retention0B_175] <;> rfl
end SpectreClusters.StageA
