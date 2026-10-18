module

public import SpectreClusters.StageATableChecksCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem compatibilityA_row0 : compatibilityRowB .hat 0 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityA_row1 : compatibilityRowB .hat 1 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityA_row2 : compatibilityRowB .hat 2 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityA_row3 : compatibilityRowB .hat 3 = true := by rfl
end SpectreClusters.StageA
