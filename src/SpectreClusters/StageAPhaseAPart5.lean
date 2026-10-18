module

public import SpectreClusters.StageAPhaseModel

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem phaseA_81 : phaseCompatibleB .hat 81 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseA_89 : phaseCompatibleB .hat 89 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseA_210 : phaseCompatibleB .hat 210 = true := by rfl
end SpectreClusters.StageA
