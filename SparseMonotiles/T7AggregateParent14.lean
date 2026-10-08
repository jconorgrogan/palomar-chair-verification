module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent14
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 1 => 248
  | 2 => 250
  | 3 => 248
  | 8 => 220
  | 9 => 246
  | 10 => 214
  | 11 => 246
  | 16 => 240
  | 17 => 214
  | 18 => 244
  | 19 => 240
  | 24 => 240
  | 25 => 248
  | 26 => 244
  | 27 => 214
  | 32 => 244
  | 33 => 244
  | 34 => 250
  | 35 => 214
  | 40 => 248
  | 41 => 244
  | 42 => 220
  | 43 => 248
  | 48 => 220
  | 49 => 220
  | 50 => 250
  | 51 => 244
  | 56 => 240
  | 57 => 250
  | 58 => 246
  | 59 => 240
  | 64 => 246
  | 65 => 250
  | 66 => 240
  | 67 => 248
  | 72 => 220
  | 73 => 220
  | 74 => 250
  | 75 => 244
  | 80 => 246
  | 81 => 250
  | 82 => 246
  | 83 => 220
  | 88 => 214
  | 89 => 246
  | 90 => 240
  | 91 => 248
  | 96 => 214
  | 97 => 246
  | 98 => 240
  | 99 => 250
  | 104 => 248
  | 105 => 240
  | 106 => 214
  | 107 => 220
  | 112 => 244
  | 113 => 214
  | 114 => 248
  | 115 => 246
  | 120 => 220
  | 121 => 244
  | 122 => 250
  | 123 => 214
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 14)
      (crossRows mate 14 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 14)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 14)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 14 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent14
