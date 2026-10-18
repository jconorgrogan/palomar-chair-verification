module

public import SpectreClusters.StageARetention0A
public import SpectreClusters.StageARetention0B
public import SpectreClusters.StageARetention1A
public import SpectreClusters.StageARetention1B
public import SpectreClusters.GridReductionWindowStages

@[expose] public section

namespace SpectreClusters.StageA

theorem stage0_checked : GridReductionWindowBinding.ChecksStage 0 := by
  intro kind i hi hout
  cases kind
  · exact rejection_of_retention 0 .hat retention0A_all i hi hout
  · exact rejection_of_retention 0 .turtle retention0B_all i hi hout

theorem stage1_checked : GridReductionWindowBinding.ChecksStage 1 := by
  intro kind i hi hout
  cases kind
  · exact rejection_of_retention 1 .hat retention1A_all i hi hout
  · exact rejection_of_retention 1 .turtle retention1B_all i hi hout

end SpectreClusters.StageA
