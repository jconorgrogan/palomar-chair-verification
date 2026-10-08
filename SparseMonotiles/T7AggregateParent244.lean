module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent244
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 0 => 244
  | 1 => 246
  | 2 => 248
  | 3 => 250
  | 4 => 250
  | 5 => 240
  | 6 => 248
  | 7 => 248
  | 16 => 220
  | 17 => 220
  | 18 => 246
  | 19 => 220
  | 20 => 214
  | 21 => 250
  | 22 => 246
  | 23 => 244
  | 32 => 240
  | 33 => 246
  | 34 => 214
  | 35 => 250
  | 36 => 244
  | 37 => 246
  | 38 => 240
  | 39 => 220
  | 48 => 240
  | 49 => 214
  | 50 => 248
  | 51 => 246
  | 52 => 244
  | 53 => 240
  | 54 => 214
  | 55 => 248
  | 64 => 244
  | 65 => 214
  | 66 => 244
  | 67 => 246
  | 68 => 250
  | 69 => 240
  | 70 => 214
  | 71 => 250
  | 80 => 248
  | 81 => 248
  | 82 => 244
  | 83 => 240
  | 84 => 220
  | 85 => 214
  | 86 => 248
  | 87 => 220
  | 96 => 220
  | 97 => 244
  | 98 => 220
  | 99 => 214
  | 100 => 250
  | 101 => 248
  | 102 => 244
  | 103 => 246
  | 112 => 240
  | 113 => 220
  | 114 => 250
  | 115 => 244
  | 116 => 246
  | 117 => 250
  | 118 => 240
  | 119 => 214
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 244)
      (crossRows mate 244 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 244)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 244)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 244 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent244
