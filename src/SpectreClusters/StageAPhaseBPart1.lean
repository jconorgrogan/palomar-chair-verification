module

public import SpectreClusters.StageAPhaseModel

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem phaseB_201 : phaseCompatibleB .turtle 201 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseB_203 : phaseCompatibleB .turtle 203 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseB_205 : phaseCompatibleB .turtle 205 = true := by rfl
set_option maxRecDepth 100000 in
theorem phaseB_212 : phaseCompatibleB .turtle 212 = true := by rfl
end SpectreClusters.StageA
