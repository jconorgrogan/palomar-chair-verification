module

public import SpectreClusters.StageDFinalChecksModel

@[expose] public section

namespace SpectreClusters.StageD
set_option maxRecDepth 100000 in
theorem row6_pairs_checked :
    (List.finRange 6).all (fun d => (List.finRange 20).all (pairCheckB 6 d)) = true := by rfl
set_option maxRecDepth 100000 in
theorem row6_unique_checked :
    (List.finRange 20).all (uniqueCheckB 6) = true := by rfl
set_option maxRecDepth 100000 in
theorem row6_basics_checked : rowBasicsB 6 = true := by rfl
end SpectreClusters.StageD
