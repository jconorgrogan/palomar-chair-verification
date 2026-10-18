module

public import SpectreClusters.StageAPhaseModel

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem phaseA_0 : phaseCompatibleB .hat 0 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseA_2 : phaseCompatibleB .hat 2 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseA_6 : phaseCompatibleB .hat 6 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseA_8 : phaseCompatibleB .hat 8 = true := by rfl
end SpectreClusters.StageA
