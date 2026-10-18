module

public import SpectreClusters.StageATableChecksCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem compatibilityA_row8 : compatibilityRowB .hat 8 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityA_row9 : compatibilityRowB .hat 9 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityA_row10 : compatibilityRowB .hat 10 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityA_row11 : compatibilityRowB .hat 11 = true := by rfl
end SpectreClusters.StageA
