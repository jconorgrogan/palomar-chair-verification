module

public import SpectreClusters.StageATableChecksCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem compatibilityB_row0 : compatibilityRowB .turtle 0 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityB_row1 : compatibilityRowB .turtle 1 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityB_row2 : compatibilityRowB .turtle 2 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityB_row3 : compatibilityRowB .turtle 3 = true := by rfl
end SpectreClusters.StageA
