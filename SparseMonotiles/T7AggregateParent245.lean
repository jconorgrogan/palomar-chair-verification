module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent245
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 8 => 214
  | 9 => 248
  | 10 => 220
  | 11 => 244
  | 12 => 246
  | 13 => 220
  | 14 => 250
  | 15 => 248
  | 24 => 244
  | 25 => 246
  | 26 => 240
  | 27 => 220
  | 28 => 214
  | 29 => 250
  | 30 => 246
  | 31 => 250
  | 40 => 250
  | 41 => 240
  | 42 => 214
  | 43 => 250
  | 44 => 248
  | 45 => 246
  | 46 => 240
  | 47 => 240
  | 56 => 220
  | 57 => 214
  | 58 => 248
  | 59 => 220
  | 60 => 244
  | 61 => 246
  | 62 => 214
  | 63 => 246
  | 72 => 240
  | 73 => 214
  | 74 => 248
  | 75 => 246
  | 76 => 244
  | 77 => 240
  | 78 => 214
  | 79 => 248
  | 88 => 250
  | 89 => 248
  | 90 => 244
  | 91 => 246
  | 92 => 220
  | 93 => 214
  | 94 => 244
  | 95 => 248
  | 104 => 246
  | 105 => 244
  | 106 => 220
  | 107 => 214
  | 108 => 250
  | 109 => 244
  | 110 => 250
  | 111 => 250
  | 120 => 240
  | 121 => 240
  | 122 => 248
  | 123 => 220
  | 124 => 220
  | 125 => 240
  | 126 => 244
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 245)
      (crossRows mate 245 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 245)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 245)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 245 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent245
