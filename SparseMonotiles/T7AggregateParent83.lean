module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent83
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
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

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 83)
      (crossRows mate 83 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 83)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 83)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 83 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent83
