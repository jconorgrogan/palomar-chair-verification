module

public import SpectreClusters.StageDFinalChecksModel

@[expose] public section

namespace SpectreClusters.StageD
set_option maxRecDepth 100000 in
theorem row10_pairs_checked :
    (List.finRange 6).all (fun d => (List.finRange 20).all (pairCheckB 10 d)) = true := by rfl
set_option maxRecDepth 100000 in
theorem row10_unique_checked :
    (List.finRange 20).all (uniqueCheckB 10) = true := by rfl
set_option maxRecDepth 100000 in
theorem row10_basics_checked : rowBasicsB 10 = true := by rfl
end SpectreClusters.StageD
