module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent96
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 32 => 214
  | 33 => 250
  | 34 => 240
  | 35 => 246
  | 36 => 248
  | 37 => 240
  | 38 => 214
  | 39 => 244
  | 40 => 220
  | 41 => 214
  | 42 => 248
  | 43 => 220
  | 44 => 244
  | 45 => 250
  | 46 => 246
  | 47 => 214
  | 48 => 246
  | 49 => 248
  | 50 => 244
  | 51 => 250
  | 52 => 220
  | 53 => 246
  | 54 => 240
  | 55 => 244
  | 56 => 250
  | 57 => 240
  | 58 => 214
  | 59 => 250
  | 60 => 248
  | 61 => 240
  | 62 => 248
  | 63 => 250
  | 96 => 244
  | 97 => 220
  | 98 => 250
  | 99 => 240
  | 100 => 246
  | 101 => 214
  | 102 => 248
  | 103 => 240
  | 104 => 240
  | 105 => 248
  | 106 => 244
  | 107 => 248
  | 108 => 220
  | 109 => 220
  | 110 => 246
  | 111 => 220
  | 112 => 214
  | 113 => 244
  | 114 => 220
  | 115 => 220
  | 116 => 250
  | 117 => 246
  | 118 => 214
  | 119 => 240
  | 120 => 246
  | 121 => 214
  | 122 => 244
  | 123 => 244
  | 124 => 250
  | 125 => 246
  | 126 => 248
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 96)
      (crossRows mate 96 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 96)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 96)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 96 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent96
