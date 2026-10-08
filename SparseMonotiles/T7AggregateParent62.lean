module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AggregateParent62
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Proposed mate indices; every used full pose is checked in the kernel. -/
def mate (_k : Fin 408) (a b : Fin 128) : Fin 408 :=
  match a.val with
  | 1 => 220
  | 2 => 240
  | 3 => 240
  | 4 => 244
  | 5 => 248
  | 6 => 220
  | 7 => 240
  | 8 => 246
  | 9 => 220
  | 10 => 246
  | 11 => 214
  | 12 => 214
  | 13 => 248
  | 14 => 244
  | 15 => 220
  | 16 => 248
  | 17 => 246
  | 18 => 214
  | 19 => 248
  | 20 => 244
  | 21 => 244
  | 22 => 220
  | 23 => 250
  | 24 => 250
  | 25 => 220
  | 26 => 250
  | 27 => 246
  | 28 => 246
  | 29 => 240
  | 30 => 214
  | 31 => 244
  | 32 => 250
  | 33 => 214
  | 34 => 244
  | 35 => 244
  | 36 => 250
  | 37 => 220
  | 38 => 250
  | 39 => 246
  | 40 => 240
  | 41 => 250
  | 42 => 246
  | 43 => 240
  | 44 => 240
  | 45 => 214
  | 46 => 248
  | 47 => 250
  | 48 => 248
  | 49 => 246
  | 50 => 240
  | 51 => 214
  | 52 => 214
  | 53 => 248
  | 54 => 244
  | 55 => 240
  | 56 => 248
  | 57 => 244
  | 58 => 220
  | 59 => 248
  | 60 => 250
  | 61 => 220
  | 62 => 246
  | 63 => 214
  | _ => 0

/-- Every root, including every empty generated block. -/
theorem all_checked : ∀ a : Fin 128,
    sparseMemberChecks 7 registryFields (childFields a) (crossFields 62)
      (crossRows mate 62 a) = true := by decide +kernel

/-- Every original source child, without a retained-row restriction. -/
theorem all_roots (a : Fin 128) : ∀ b ∈ children7,
    CellContact (sourceChild a) (compose (dilatePose (registry 62)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry 62)) b) ∈ M7 :=
  generated_cross_block (crossRows_binding mate 62 a) (all_checked a)

#print axioms all_checked
#print axioms all_roots
end SparseMonotiles.CarrierHierarchy.T7AggregateParent62
