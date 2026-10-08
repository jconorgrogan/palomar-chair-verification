module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent18
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 2 => 214
  | 3 => 246
  | 6 => 244
  | 7 => 214
  | 10 => 250
  | 11 => 248
  | 14 => 220
  | 15 => 244
  | 18 => 240
  | 19 => 244
  | 22 => 250
  | 23 => 220
  | 26 => 246
  | 27 => 250
  | 30 => 240
  | 31 => 220
  | 34 => 248
  | 35 => 220
  | 38 => 246
  | 39 => 250
  | 42 => 240
  | 43 => 246
  | 46 => 214
  | 47 => 246
  | 50 => 214
  | 51 => 240
  | 54 => 248
  | 55 => 214
  | 58 => 244
  | 59 => 244
  | 62 => 240
  | 63 => 240
  | 66 => 220
  | 67 => 250
  | 70 => 240
  | 71 => 246
  | 74 => 214
  | 75 => 240
  | 78 => 248
  | 79 => 214
  | 82 => 248
  | 83 => 214
  | 86 => 244
  | 87 => 244
  | 90 => 220
  | 91 => 250
  | 94 => 248
  | 95 => 244
  | 98 => 244
  | 99 => 248
  | 102 => 220
  | 103 => 250
  | 106 => 250
  | 107 => 240
  | 110 => 220
  | 111 => 246
  | 114 => 246
  | 115 => 248
  | 118 => 246
  | 119 => 248
  | 122 => 214
  | 123 => 250
  | 126 => 220
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 18)
      (crossRows mate 18 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 18)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 18)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 18 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent18
