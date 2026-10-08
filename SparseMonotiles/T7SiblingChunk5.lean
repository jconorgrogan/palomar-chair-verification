module
public import SparseMonotiles.T7SiblingData
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7SiblingChunk5
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows T7SiblingData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Complete checks for roots80–95, restricted only by the root number. -/
theorem checked : ∀ a : Fin 128, 80 ≤ a.val → a.val < 96 →
    sparseMemberChecks 7 registryFields (childFields a) childFields (siblingRows siblingMate a) = true := by
  decide +kernel

#print axioms checked
end SparseMonotiles.CarrierHierarchy.T7SiblingChunk5
