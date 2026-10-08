module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent332
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 1 => 214
  | 3 => 244
  | 5 => 250
  | 7 => 220
  | 9 => 240
  | 11 => 250
  | 13 => 246
  | 15 => 240
  | 17 => 248
  | 19 => 246
  | 21 => 240
  | 23 => 214
  | 25 => 214
  | 27 => 248
  | 29 => 244
  | 31 => 240
  | 33 => 220
  | 35 => 240
  | 37 => 214
  | 39 => 248
  | 41 => 248
  | 43 => 244
  | 45 => 220
  | 47 => 248
  | 49 => 244
  | 51 => 220
  | 53 => 250
  | 55 => 220
  | 57 => 246
  | 59 => 246
  | 61 => 214
  | 63 => 220
  | 65 => 246
  | 67 => 214
  | 69 => 248
  | 71 => 244
  | 73 => 244
  | 75 => 220
  | 77 => 250
  | 79 => 220
  | 81 => 220
  | 83 => 250
  | 85 => 246
  | 87 => 246
  | 89 => 240
  | 91 => 214
  | 93 => 244
  | 95 => 240
  | 97 => 250
  | 99 => 246
  | 101 => 240
  | 103 => 214
  | 105 => 214
  | 107 => 244
  | 109 => 250
  | 111 => 244
  | 113 => 248
  | 115 => 250
  | 117 => 240
  | 119 => 246
  | 121 => 248
  | 123 => 248
  | 125 => 250
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 332)
      (crossRows mate 332 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 332)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 332)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 332 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent332
