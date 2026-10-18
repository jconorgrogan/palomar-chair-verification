module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0APart17
public import SpectreClusters.StageAReject0APart18
public import SpectreClusters.StageAReject0APart19
public import SpectreClusters.StageAReject0APart20

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0A_96 : retentionCheckB 0 .hat 96 = true :=
  retention_of_rejected 0 .hat 96 reject0A_96
theorem retention0A_97 : retentionCheckB 0 .hat 97 = true :=
  retention_of_rejected 0 .hat 97 reject0A_97
theorem retention0A_98 : retentionCheckB 0 .hat 98 = true :=
  retention_of_rejected 0 .hat 98 reject0A_98
theorem retention0A_99 : retentionCheckB 0 .hat 99 = true :=
  retention_of_rejected 0 .hat 99 reject0A_99
theorem retention0A_100 : retentionCheckB 0 .hat 100 = true :=
  retention_of_rejected 0 .hat 100 reject0A_100
theorem retention0A_101 : retentionCheckB 0 .hat 101 = true :=
  retention_of_rejected 0 .hat 101 reject0A_101
theorem retention0A_102 : retentionCheckB 0 .hat 102 = true :=
  retention_of_rejected 0 .hat 102 reject0A_102
theorem retention0A_103 : retentionCheckB 0 .hat 103 = true :=
  retention_of_rejected 0 .hat 103 reject0A_103
theorem retention0A_104 : retentionCheckB 0 .hat 104 = true :=
  retention_of_rejected 0 .hat 104 reject0A_104
theorem retention0A_105 : retentionCheckB 0 .hat 105 = true :=
  retention_of_rejected 0 .hat 105 reject0A_105
theorem retention0A_106 : retentionCheckB 0 .hat 106 = true :=
  retention_of_rejected 0 .hat 106 reject0A_106
theorem retention0A_107 : retentionCheckB 0 .hat 107 = true :=
  retention_of_rejected 0 .hat 107 reject0A_107
theorem retention0A_108 : retentionCheckB 0 .hat 108 = true :=
  retention_of_rejected 0 .hat 108 reject0A_108
theorem retention0A_109 : retentionCheckB 0 .hat 109 = true :=
  retention_of_rejected 0 .hat 109 reject0A_109
theorem retention0A_110 : retentionCheckB 0 .hat 110 = true :=
  retention_of_rejected 0 .hat 110 reject0A_110
theorem retention0A_111 : retentionCheckB 0 .hat 111 = true :=
  retention_of_rejected 0 .hat 111 reject0A_111
theorem retention0A_block6 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111].all (retentionCheckB 0 .hat) = true := by
  simp only [List.all_cons,List.all_nil,retention0A_96, retention0A_97, retention0A_98, retention0A_99, retention0A_100, retention0A_101, retention0A_102, retention0A_103, retention0A_104, retention0A_105, retention0A_106, retention0A_107, retention0A_108, retention0A_109, retention0A_110, retention0A_111] <;> rfl
end SpectreClusters.StageA
