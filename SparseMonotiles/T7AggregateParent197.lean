module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent197
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 16 => 214
  | 17 => 240
  | 18 => 248
  | 19 => 214
  | 20 => 220
  | 21 => 248
  | 22 => 244
  | 23 => 246
  | 24 => 246
  | 25 => 244
  | 26 => 220
  | 27 => 240
  | 28 => 250
  | 29 => 214
  | 30 => 248
  | 31 => 248
  | 48 => 244
  | 49 => 250
  | 50 => 246
  | 51 => 248
  | 52 => 240
  | 53 => 244
  | 54 => 220
  | 55 => 246
  | 56 => 214
  | 57 => 220
  | 58 => 250
  | 59 => 214
  | 60 => 246
  | 61 => 244
  | 62 => 250
  | 63 => 248
  | 80 => 250
  | 81 => 246
  | 82 => 240
  | 83 => 244
  | 84 => 214
  | 85 => 220
  | 86 => 250
  | 87 => 214
  | 88 => 248
  | 89 => 250
  | 90 => 246
  | 91 => 244
  | 92 => 240
  | 93 => 250
  | 94 => 240
  | 95 => 250
  | 112 => 220
  | 113 => 240
  | 114 => 214
  | 115 => 240
  | 116 => 248
  | 117 => 248
  | 118 => 220
  | 119 => 220
  | 120 => 244
  | 121 => 220
  | 122 => 246
  | 123 => 240
  | 124 => 214
  | 125 => 244
  | 126 => 246
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 197)
      (crossRows mate 197 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 197)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 197)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 197 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent197
