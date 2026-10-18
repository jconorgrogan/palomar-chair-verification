module

public import SpectreClusters.StageDFinalChecksModel

@[expose] public section

namespace SpectreClusters.StageD
set_option maxRecDepth 100000 in
theorem row9_pairs_checked :
    (List.finRange 6).all (fun d => (List.finRange 20).all (pairCheckB 9 d)) = true := by rfl
set_option maxRecDepth 100000 in
theorem row9_unique_checked :
    (List.finRange 20).all (uniqueCheckB 9) = true := by rfl
set_option maxRecDepth 100000 in
theorem row9_basics_checked : rowBasicsB 9 = true := by rfl
end SpectreClusters.StageD
