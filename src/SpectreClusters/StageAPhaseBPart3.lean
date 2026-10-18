module

public import SpectreClusters.StageAPhaseModel

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem phaseB_222 : phaseCompatibleB .turtle 222 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseB_223 : phaseCompatibleB .turtle 223 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseB_226 : phaseCompatibleB .turtle 226 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseB_227 : phaseCompatibleB .turtle 227 = true := by rfl
end SpectreClusters.StageA
