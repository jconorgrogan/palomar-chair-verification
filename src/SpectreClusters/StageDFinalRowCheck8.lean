module

public import SpectreClusters.StageDFinalChecksModel

@[expose] public section

namespace SpectreClusters.StageD
set_option maxRecDepth 100000 in
theorem row8_pairs_checked :
    (List.finRange 6).all (fun d => (List.finRange 20).all (pairCheckB 8 d)) = true := by rfl
set_option maxRecDepth 100000 in
theorem row8_unique_checked :
    (List.finRange 20).all (uniqueCheckB 8) = true := by rfl
set_option maxRecDepth 100000 in
theorem row8_basics_checked : rowBasicsB 8 = true := by rfl
end SpectreClusters.StageD
