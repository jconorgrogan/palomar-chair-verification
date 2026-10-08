module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent57
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 1 => 250
  | 4 => 220
  | 5 => 214
  | 8 => 240
  | 9 => 244
  | 12 => 240
  | 13 => 244
  | 16 => 244
  | 17 => 250
  | 20 => 248
  | 21 => 220
  | 24 => 220
  | 25 => 250
  | 28 => 240
  | 29 => 246
  | 32 => 246
  | 33 => 240
  | 36 => 220
  | 37 => 250
  | 40 => 246
  | 41 => 246
  | 44 => 214
  | 45 => 240
  | 48 => 214
  | 49 => 240
  | 52 => 248
  | 53 => 214
  | 56 => 244
  | 57 => 248
  | 60 => 220
  | 61 => 250
  | 64 => 248
  | 65 => 248
  | 68 => 246
  | 69 => 246
  | 72 => 214
  | 73 => 240
  | 76 => 248
  | 77 => 214
  | 80 => 244
  | 81 => 214
  | 84 => 244
  | 85 => 248
  | 88 => 220
  | 89 => 244
  | 92 => 250
  | 93 => 240
  | 96 => 250
  | 97 => 248
  | 100 => 220
  | 101 => 244
  | 104 => 250
  | 105 => 220
  | 108 => 246
  | 109 => 248
  | 112 => 246
  | 113 => 250
  | 116 => 240
  | 117 => 220
  | 120 => 214
  | 121 => 246
  | 124 => 244
  | 125 => 214
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 57)
      (crossRows mate 57 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 57)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 57)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 57 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent57
