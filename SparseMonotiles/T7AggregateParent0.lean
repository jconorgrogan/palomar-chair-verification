module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent0
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed catalog indices. All values used by the complete generated
rows are certified by full-pose field comparisons below. -/
def mate (_k : Fin 408) (a _b : Fin 128) : Fin 408 :=
  match a.val with
  | 63 => 388
  | 95 => 358
  | 111 => 332
  | 119 => 306
  | 123 => 280
  | 125 => 254
  | 126 => 225
  | 127 => 239
  | _ => 0

/-- Kernel certification for every root role, including every empty block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 0)
      (crossRows mate 0 a) = true := by decide +kernel

/-- Complete cross-parent ForwardRules block for the exact original parent 0.
The source child ranges over all children7, not just the retained rows. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 0)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 0)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 0 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent0
