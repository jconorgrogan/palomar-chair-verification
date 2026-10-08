module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent7
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 1 => 240
  | 2 => 244
  | 3 => 220
  | 4 => 246
  | 5 => 246
  | 6 => 214
  | 7 => 244
  | 8 => 248
  | 9 => 214
  | 10 => 244
  | 11 => 220
  | 12 => 250
  | 13 => 250
  | 14 => 246
  | 15 => 214
  | 16 => 250
  | 17 => 244
  | 18 => 250
  | 19 => 250
  | 20 => 240
  | 21 => 246
  | 22 => 240
  | 23 => 248
  | 24 => 248
  | 25 => 240
  | 26 => 214
  | 27 => 244
  | 28 => 248
  | 29 => 220
  | 30 => 250
  | 31 => 246
  | 64 => 220
  | 65 => 240
  | 66 => 248
  | 67 => 240
  | 68 => 220
  | 69 => 214
  | 70 => 248
  | 71 => 220
  | 72 => 246
  | 73 => 248
  | 74 => 244
  | 75 => 250
  | 76 => 220
  | 77 => 246
  | 78 => 240
  | 79 => 244
  | 80 => 214
  | 81 => 244
  | 82 => 220
  | 83 => 246
  | 84 => 250
  | 85 => 240
  | 86 => 214
  | 87 => 250
  | 88 => 246
  | 89 => 214
  | 90 => 248
  | 91 => 240
  | 92 => 244
  | 93 => 248
  | 94 => 220
  | 95 => 214
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 7)
      (crossRows mate 7 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 7)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 7)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 7 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent7
