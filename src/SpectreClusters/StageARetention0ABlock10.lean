module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart33
public import SpectreClusters.StageAReject0APart34
public import SpectreClusters.StageAReject0APart35
public import SpectreClusters.StageAReject0APart36

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_160 : retentionCheckB 0 .hat 160 = true :=
  retention_of_rejected 0 .hat 160 reject0A_160
theorem retention0A_161 : retentionCheckB 0 .hat 161 = true :=
  retention_of_rejected 0 .hat 161 reject0A_161
theorem retention0A_162 : retentionCheckB 0 .hat 162 = true :=
  retention_of_rejected 0 .hat 162 reject0A_162
theorem retention0A_163 : retentionCheckB 0 .hat 163 = true :=
  retention_of_rejected 0 .hat 163 reject0A_163
theorem retention0A_164 : retentionCheckB 0 .hat 164 = true :=
  retention_of_rejected 0 .hat 164 reject0A_164
theorem retention0A_165 : retentionCheckB 0 .hat 165 = true :=
  retention_of_rejected 0 .hat 165 reject0A_165
theorem retention0A_166 : retentionCheckB 0 .hat 166 = true :=
  retention_of_rejected 0 .hat 166 reject0A_166
theorem retention0A_167 : retentionCheckB 0 .hat 167 = true :=
  retention_of_rejected 0 .hat 167 reject0A_167
theorem retention0A_168 : retentionCheckB 0 .hat 168 = true :=
  retention_of_rejected 0 .hat 168 reject0A_168
theorem retention0A_169 : retentionCheckB 0 .hat 169 = true :=
  retention_of_rejected 0 .hat 169 reject0A_169
theorem retention0A_170 : retentionCheckB 0 .hat 170 = true :=
  retention_of_rejected 0 .hat 170 reject0A_170
theorem retention0A_171 : retentionCheckB 0 .hat 171 = true :=
  retention_of_rejected 0 .hat 171 reject0A_171
theorem retention0A_172 : retentionCheckB 0 .hat 172 = true :=
  retention_of_rejected 0 .hat 172 reject0A_172
theorem retention0A_173 : retentionCheckB 0 .hat 173 = true :=
  retention_of_rejected 0 .hat 173 reject0A_173
theorem retention0A_174 : retentionCheckB 0 .hat 174 = true :=
  retention_of_rejected 0 .hat 174 reject0A_174
theorem retention0A_175 : retentionCheckB 0 .hat 175 = true :=
  retention_of_rejected 0 .hat 175 reject0A_175
theorem retention0A_block10 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_160, retention0A_161, retention0A_162, retention0A_163, retention0A_164, retention0A_165, retention0A_166, retention0A_167, retention0A_168, retention0A_169, retention0A_170, retention0A_171, retention0A_172, retention0A_173, retention0A_174, retention0A_175] <;> rfl
end SpectreClusters.StageA
