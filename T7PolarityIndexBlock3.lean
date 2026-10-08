module
public import T7PolarityIndexBase
@[expose] public section
namespace SparseMonotiles.T7PolarityIndexing
open Contact CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem coverBlock3 : allPairsB
    (fun (_ : Fin 1) (i : Fin 256) => checkCover ⟨768 + i.val, by omega⟩) = true := by decide +kernel
#print axioms coverBlock3
end SparseMonotiles.T7PolarityIndexing
