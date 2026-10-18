module

public import SpectreClusters.StageATableChecksCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem compatibilityB_row4 : compatibilityRowB .turtle 4 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityB_row5 : compatibilityRowB .turtle 5 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityB_row6 : compatibilityRowB .turtle 6 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityB_row7 : compatibilityRowB .turtle 7 = true := by rfl
end SpectreClusters.StageA
