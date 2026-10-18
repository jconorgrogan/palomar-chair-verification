module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart35
public import SpectreClusters.StageAReject0BPart36
public import SpectreClusters.StageAReject0BPart37
public import SpectreClusters.StageAReject0BPart38
public import SpectreClusters.StageAReject0BPart39

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_144 : retentionCheckB 0 .turtle 144 = true :=
  retention_of_rejected 0 .turtle 144 reject0B_144
theorem retention0B_145 : retentionCheckB 0 .turtle 145 = true :=
  retention_of_rejected 0 .turtle 145 reject0B_145
theorem retention0B_146 : retentionCheckB 0 .turtle 146 = true :=
  retention_of_rejected 0 .turtle 146 reject0B_146
theorem retention0B_147 : retentionCheckB 0 .turtle 147 = true :=
  retention_of_rejected 0 .turtle 147 reject0B_147
theorem retention0B_148 : retentionCheckB 0 .turtle 148 = true :=
  retention_of_rejected 0 .turtle 148 reject0B_148
theorem retention0B_149 : retentionCheckB 0 .turtle 149 = true :=
  retention_of_rejected 0 .turtle 149 reject0B_149
theorem retention0B_150 : retentionCheckB 0 .turtle 150 = true :=
  retention_of_rejected 0 .turtle 150 reject0B_150
theorem retention0B_151 : retentionCheckB 0 .turtle 151 = true :=
  retention_of_rejected 0 .turtle 151 reject0B_151
theorem retention0B_152 : retentionCheckB 0 .turtle 152 = true :=
  retention_of_rejected 0 .turtle 152 reject0B_152
theorem retention0B_153 : retentionCheckB 0 .turtle 153 = true :=
  retention_of_rejected 0 .turtle 153 reject0B_153
theorem retention0B_154 : retentionCheckB 0 .turtle 154 = true :=
  retention_of_rejected 0 .turtle 154 reject0B_154
theorem retention0B_155 : retentionCheckB 0 .turtle 155 = true :=
  retention_of_rejected 0 .turtle 155 reject0B_155
theorem retention0B_156 : retentionCheckB 0 .turtle 156 = true :=
  retention_of_rejected 0 .turtle 156 reject0B_156
theorem retention0B_157 : retentionCheckB 0 .turtle 157 = true :=
  retention_of_rejected 0 .turtle 157 reject0B_157
theorem retention0B_158 : retentionCheckB 0 .turtle 158 = true :=
  retention_of_rejected 0 .turtle 158 reject0B_158
theorem retention0B_159 : retentionCheckB 0 .turtle 159 = true :=
  retention_of_rejected 0 .turtle 159 reject0B_159
theorem retention0B_block9 : [144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_144, retention0B_145, retention0B_146, retention0B_147, retention0B_148, retention0B_149, retention0B_150, retention0B_151, retention0B_152, retention0B_153, retention0B_154, retention0B_155, retention0B_156, retention0B_157, retention0B_158, retention0B_159] <;> rfl
end SpectreClusters.StageA
