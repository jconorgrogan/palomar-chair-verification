module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent293
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 4 => 214
  | 5 => 220
  | 6 => 246
  | 7 => 250
  | 12 => 244
  | 13 => 240
  | 14 => 214
  | 15 => 246
  | 20 => 250
  | 21 => 214
  | 22 => 248
  | 23 => 240
  | 28 => 220
  | 29 => 248
  | 30 => 244
  | 31 => 214
  | 36 => 240
  | 37 => 248
  | 38 => 244
  | 39 => 214
  | 44 => 250
  | 45 => 244
  | 46 => 220
  | 47 => 244
  | 52 => 246
  | 53 => 220
  | 54 => 250
  | 55 => 250
  | 60 => 240
  | 61 => 248
  | 62 => 220
  | 63 => 244
  | 68 => 248
  | 69 => 244
  | 70 => 220
  | 71 => 248
  | 76 => 246
  | 77 => 220
  | 78 => 250
  | 79 => 250
  | 84 => 240
  | 85 => 250
  | 86 => 246
  | 87 => 240
  | 92 => 214
  | 93 => 220
  | 94 => 246
  | 95 => 246
  | 100 => 214
  | 101 => 246
  | 102 => 240
  | 103 => 248
  | 108 => 248
  | 109 => 246
  | 110 => 214
  | 111 => 248
  | 116 => 244
  | 117 => 214
  | 118 => 244
  | 119 => 250
  | 124 => 240
  | 125 => 220
  | 126 => 240
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 293)
      (crossRows mate 293 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 293)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 293)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 293 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent293
