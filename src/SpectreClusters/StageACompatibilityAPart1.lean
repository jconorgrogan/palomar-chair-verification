module

public import SpectreClusters.StageATableChecksCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem compatibilityA_row4 : compatibilityRowB .hat 4 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityA_row5 : compatibilityRowB .hat 5 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityA_row6 : compatibilityRowB .hat 6 = true := by rfl
set_option maxRecDepth 100000 in
theorem compatibilityA_row7 : compatibilityRowB .hat 7 = true := by rfl
end SpectreClusters.StageA
