module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent196
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 1 => 244
  | 2 => 246
  | 3 => 214
  | 4 => 248
  | 5 => 244
  | 6 => 250
  | 7 => 246
  | 8 => 250
  | 9 => 250
  | 10 => 240
  | 11 => 240
  | 12 => 248
  | 13 => 214
  | 14 => 248
  | 15 => 250
  | 32 => 220
  | 33 => 248
  | 34 => 220
  | 35 => 248
  | 36 => 246
  | 37 => 244
  | 38 => 220
  | 39 => 240
  | 40 => 214
  | 41 => 220
  | 42 => 250
  | 43 => 214
  | 44 => 246
  | 45 => 248
  | 46 => 244
  | 47 => 220
  | 64 => 240
  | 65 => 220
  | 66 => 246
  | 67 => 244
  | 68 => 214
  | 69 => 220
  | 70 => 250
  | 71 => 214
  | 72 => 244
  | 73 => 250
  | 74 => 246
  | 75 => 248
  | 76 => 240
  | 77 => 244
  | 78 => 220
  | 79 => 246
  | 96 => 240
  | 97 => 240
  | 98 => 214
  | 99 => 220
  | 100 => 248
  | 101 => 250
  | 102 => 246
  | 103 => 244
  | 104 => 244
  | 105 => 246
  | 106 => 240
  | 107 => 250
  | 108 => 214
  | 109 => 240
  | 110 => 248
  | 111 => 214
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 196)
      (crossRows mate 196 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 196)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 196)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 196 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent196
