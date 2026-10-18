module

public import SpectreClusters.StageARetentionCore
public import SpectreClusters.StageAReject0BPart7
public import SpectreClusters.StageAReject0BPart8
public import SpectreClusters.StageAReject0BPart9
public import SpectreClusters.StageAReject0BPart10
public import SpectreClusters.StageAReject0BPart11

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem retention0B_32 : retentionCheckB 0 .turtle 32 = true :=
  retention_of_rejected 0 .turtle 32 reject0B_32
theorem retention0B_33 : retentionCheckB 0 .turtle 33 = true :=
  retention_of_rejected 0 .turtle 33 reject0B_33
theorem retention0B_34 : retentionCheckB 0 .turtle 34 = true :=
  retention_of_rejected 0 .turtle 34 reject0B_34
theorem retention0B_35 : retentionCheckB 0 .turtle 35 = true :=
  retention_of_rejected 0 .turtle 35 reject0B_35
theorem retention0B_36 : retentionCheckB 0 .turtle 36 = true :=
  retention_of_rejected 0 .turtle 36 reject0B_36
theorem retention0B_37 : retentionCheckB 0 .turtle 37 = true :=
  retention_of_rejected 0 .turtle 37 reject0B_37
theorem retention0B_38 : retentionCheckB 0 .turtle 38 = true :=
  retention_of_rejected 0 .turtle 38 reject0B_38
theorem retention0B_39 : retentionCheckB 0 .turtle 39 = true :=
  retention_of_rejected 0 .turtle 39 reject0B_39
theorem retention0B_40 : retentionCheckB 0 .turtle 40 = true :=
  retention_of_rejected 0 .turtle 40 reject0B_40
theorem retention0B_41 : retentionCheckB 0 .turtle 41 = true :=
  retention_of_rejected 0 .turtle 41 reject0B_41
theorem retention0B_42 : retentionCheckB 0 .turtle 42 = true :=
  retention_of_rejected 0 .turtle 42 reject0B_42
theorem retention0B_43 : retentionCheckB 0 .turtle 43 = true :=
  retention_of_rejected 0 .turtle 43 reject0B_43
theorem retention0B_44 : retentionCheckB 0 .turtle 44 = true :=
  retention_of_rejected 0 .turtle 44 reject0B_44
theorem retention0B_45 : retentionCheckB 0 .turtle 45 = true :=
  retention_of_rejected 0 .turtle 45 reject0B_45
theorem retention0B_46 : retentionCheckB 0 .turtle 46 = true :=
  retention_of_rejected 0 .turtle 46 reject0B_46
theorem retention0B_47 : retentionCheckB 0 .turtle 47 = true :=
  retention_of_rejected 0 .turtle 47 reject0B_47
theorem retention0B_block2 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47].all (retentionCheckB 0 .turtle) = true := by
  simp only [List.all_cons,List.all_nil,retention0B_32, retention0B_33, retention0B_34, retention0B_35, retention0B_36, retention0B_37, retention0B_38, retention0B_39, retention0B_40, retention0B_41, retention0B_42, retention0B_43, retention0B_44, retention0B_45, retention0B_46, retention0B_47] <;> rfl
end SpectreClusters.StageA
