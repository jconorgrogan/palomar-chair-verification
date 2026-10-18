module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart21
public import SpectreClusters.StageAReject0APart22
public import SpectreClusters.StageAReject0APart23
public import SpectreClusters.StageAReject0APart24

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_112 : retentionCheckB 0 .hat 112 = true :=
  retention_of_rejected 0 .hat 112 reject0A_112
theorem retention0A_113 : retentionCheckB 0 .hat 113 = true :=
  retention_of_rejected 0 .hat 113 reject0A_113
theorem retention0A_114 : retentionCheckB 0 .hat 114 = true :=
  retention_of_rejected 0 .hat 114 reject0A_114
theorem retention0A_115 : retentionCheckB 0 .hat 115 = true :=
  retention_of_rejected 0 .hat 115 reject0A_115
theorem retention0A_116 : retentionCheckB 0 .hat 116 = true :=
  retention_of_rejected 0 .hat 116 reject0A_116
theorem retention0A_117 : retentionCheckB 0 .hat 117 = true :=
  retention_of_rejected 0 .hat 117 reject0A_117
theorem retention0A_118 : retentionCheckB 0 .hat 118 = true :=
  retention_of_rejected 0 .hat 118 reject0A_118
theorem retention0A_119 : retentionCheckB 0 .hat 119 = true :=
  retention_of_rejected 0 .hat 119 reject0A_119
theorem retention0A_120 : retentionCheckB 0 .hat 120 = true :=
  retention_of_rejected 0 .hat 120 reject0A_120
theorem retention0A_121 : retentionCheckB 0 .hat 121 = true :=
  retention_of_rejected 0 .hat 121 reject0A_121
theorem retention0A_122 : retentionCheckB 0 .hat 122 = true :=
  retention_of_rejected 0 .hat 122 reject0A_122
theorem retention0A_123 : retentionCheckB 0 .hat 123 = true :=
  retention_of_rejected 0 .hat 123 reject0A_123
theorem retention0A_124 : retentionCheckB 0 .hat 124 = true :=
  retention_of_rejected 0 .hat 124 reject0A_124
theorem retention0A_125 : retentionCheckB 0 .hat 125 = true :=
  retention_of_rejected 0 .hat 125 reject0A_125
theorem retention0A_126 : retentionCheckB 0 .hat 126 = true :=
  retention_of_rejected 0 .hat 126 reject0A_126
theorem retention0A_127 : retentionCheckB 0 .hat 127 = true :=
  retention_of_rejected 0 .hat 127 reject0A_127
theorem retention0A_block7 : [112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_112, retention0A_113, retention0A_114, retention0A_115, retention0A_116, retention0A_117, retention0A_118, retention0A_119, retention0A_120, retention0A_121, retention0A_122, retention0A_123, retention0A_124, retention0A_125, retention0A_126, retention0A_127] <;> rfl
end SpectreClusters.StageA
