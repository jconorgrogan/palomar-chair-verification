module

public import SpectreClusters.StageDFinalChecksModel

@[expose] public section

namespace SpectreClusters.StageD
set_option maxRecDepth 100000 in
theorem row1_pairs_checked :
    (List.finRange 6).all (fun d => (List.finRange 20).all (pairCheckB 1 d)) = true := by rfl
set_option maxRecDepth 100000 in
theorem row1_unique_checked :
    (List.finRange 20).all (uniqueCheckB 1) = true := by rfl
set_option maxRecDepth 100000 in
theorem row1_basics_checked : rowBasicsB 1 = true := by rfl
end SpectreClusters.StageD
