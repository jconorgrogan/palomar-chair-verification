module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart23
public import SpectreClusters.StageAReject0BPart24
public import SpectreClusters.StageAReject0BPart25
public import SpectreClusters.StageAReject0BPart26
public import SpectreClusters.StageAReject0BPart27

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_96 : retentionCheckB 0 .turtle 96 = true :=
  retention_of_rejected 0 .turtle 96 reject0B_96
theorem retention0B_97 : retentionCheckB 0 .turtle 97 = true :=
  retention_of_rejected 0 .turtle 97 reject0B_97
theorem retention0B_98 : retentionCheckB 0 .turtle 98 = true :=
  retention_of_rejected 0 .turtle 98 reject0B_98
theorem retention0B_99 : retentionCheckB 0 .turtle 99 = true :=
  retention_of_rejected 0 .turtle 99 reject0B_99
theorem retention0B_100 : retentionCheckB 0 .turtle 100 = true :=
  retention_of_rejected 0 .turtle 100 reject0B_100
theorem retention0B_101 : retentionCheckB 0 .turtle 101 = true :=
  retention_of_rejected 0 .turtle 101 reject0B_101
theorem retention0B_102 : retentionCheckB 0 .turtle 102 = true :=
  retention_of_rejected 0 .turtle 102 reject0B_102
theorem retention0B_103 : retentionCheckB 0 .turtle 103 = true :=
  retention_of_rejected 0 .turtle 103 reject0B_103
theorem retention0B_104 : retentionCheckB 0 .turtle 104 = true :=
  retention_of_rejected 0 .turtle 104 reject0B_104
theorem retention0B_105 : retentionCheckB 0 .turtle 105 = true :=
  retention_of_rejected 0 .turtle 105 reject0B_105
theorem retention0B_106 : retentionCheckB 0 .turtle 106 = true :=
  retention_of_rejected 0 .turtle 106 reject0B_106
theorem retention0B_107 : retentionCheckB 0 .turtle 107 = true :=
  retention_of_rejected 0 .turtle 107 reject0B_107
theorem retention0B_108 : retentionCheckB 0 .turtle 108 = true :=
  retention_of_rejected 0 .turtle 108 reject0B_108
theorem retention0B_109 : retentionCheckB 0 .turtle 109 = true :=
  retention_of_rejected 0 .turtle 109 reject0B_109
theorem retention0B_110 : retentionCheckB 0 .turtle 110 = true :=
  retention_of_rejected 0 .turtle 110 reject0B_110
theorem retention0B_111 : retentionCheckB 0 .turtle 111 = true :=
  retention_of_rejected 0 .turtle 111 reject0B_111
theorem retention0B_block6 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_96, retention0B_97, retention0B_98, retention0B_99, retention0B_100, retention0B_101, retention0B_102, retention0B_103, retention0B_104, retention0B_105, retention0B_106, retention0B_107, retention0B_108, retention0B_109, retention0B_110, retention0B_111] <;> rfl
end SpectreClusters.StageA
