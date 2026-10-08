module
public import ReplayLeafR445C0
public import ReplayLeafR445C1
namespace SparseMonotiles.FullContactReplay.Root445
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified (b : Fin 512) : PairLaw 445 b := by
  by_cases hb : b.val < 256
  · have h := LeafR445C0.classified ⟨b.val, by omega⟩
    have he : sourceBlock256 0 ⟨b.val, by omega⟩ = b := by apply Fin.ext; simp only [sourceBlock256]; omega
    simpa only [he] using h
  · have h := LeafR445C1.classified ⟨b.val - 256, by omega⟩
    have he : sourceBlock256 1 ⟨b.val - 256, by omega⟩ = b := by apply Fin.ext; simp only [sourceBlock256]; omega
    simpa only [he] using h
#print axioms classified
end SparseMonotiles.FullContactReplay.Root445
