module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent356
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 2 => 220
  | 4 => 240
  | 6 => 240
  | 8 => 244
  | 10 => 248
  | 12 => 220
  | 14 => 240
  | 16 => 246
  | 18 => 220
  | 20 => 246
  | 22 => 214
  | 24 => 214
  | 26 => 248
  | 28 => 244
  | 30 => 220
  | 32 => 248
  | 34 => 246
  | 36 => 214
  | 38 => 248
  | 40 => 244
  | 42 => 244
  | 44 => 220
  | 46 => 250
  | 48 => 250
  | 50 => 220
  | 52 => 250
  | 54 => 246
  | 56 => 246
  | 58 => 240
  | 60 => 214
  | 62 => 244
  | 64 => 250
  | 66 => 214
  | 68 => 244
  | 70 => 244
  | 72 => 250
  | 74 => 220
  | 76 => 250
  | 78 => 246
  | 80 => 240
  | 82 => 250
  | 84 => 246
  | 86 => 240
  | 88 => 240
  | 90 => 214
  | 92 => 248
  | 94 => 250
  | 96 => 248
  | 98 => 246
  | 100 => 240
  | 102 => 214
  | 104 => 214
  | 106 => 248
  | 108 => 244
  | 110 => 240
  | 112 => 248
  | 114 => 244
  | 116 => 220
  | 118 => 248
  | 120 => 250
  | 122 => 220
  | 124 => 246
  | 126 => 214
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 356)
      (crossRows mate 356 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 356)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 356)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 356 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent356
