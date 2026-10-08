module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent63
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 64 => 214
  | 65 => 244
  | 66 => 250
  | 67 => 220
  | 68 => 240
  | 69 => 250
  | 70 => 246
  | 71 => 240
  | 72 => 248
  | 73 => 246
  | 74 => 240
  | 75 => 214
  | 76 => 214
  | 77 => 248
  | 78 => 244
  | 79 => 240
  | 80 => 220
  | 81 => 240
  | 82 => 214
  | 83 => 248
  | 84 => 248
  | 85 => 244
  | 86 => 220
  | 87 => 248
  | 88 => 244
  | 89 => 220
  | 90 => 250
  | 91 => 220
  | 92 => 246
  | 93 => 246
  | 94 => 214
  | 95 => 220
  | 96 => 246
  | 97 => 214
  | 98 => 248
  | 99 => 244
  | 100 => 244
  | 101 => 220
  | 102 => 250
  | 103 => 220
  | 104 => 220
  | 105 => 250
  | 106 => 246
  | 107 => 246
  | 108 => 240
  | 109 => 214
  | 110 => 244
  | 111 => 240
  | 112 => 250
  | 113 => 246
  | 114 => 240
  | 115 => 214
  | 116 => 214
  | 117 => 244
  | 118 => 250
  | 119 => 244
  | 120 => 248
  | 121 => 250
  | 122 => 240
  | 123 => 246
  | 124 => 248
  | 125 => 248
  | 126 => 250
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 63)
      (crossRows mate 63 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 63)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 63)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 63 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent63
