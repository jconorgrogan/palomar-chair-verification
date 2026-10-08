module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents64–95; all128 roots and every generated role. -/
theorem cross_checks_group2 (k : Fin 408) (hl : 64 ≤ k.val) (hu : k.val < 96)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h64 : k.val = 64
  · have hk : k = 64 := Fin.ext h64
    subst k
    exact T7AggregateParent64.all_checked a
  by_cases h65 : k.val = 65
  · have hk : k = 65 := Fin.ext h65
    subst k
    exact T7AggregateParent65.all_checked a
  by_cases h66 : k.val = 66
  · have hk : k = 66 := Fin.ext h66
    subst k
    exact T7AggregateParent66.all_checked a
  by_cases h67 : k.val = 67
  · have hk : k = 67 := Fin.ext h67
    subst k
    exact T7AggregateParent67.all_checked a
  by_cases h68 : k.val = 68
  · have hk : k = 68 := Fin.ext h68
    subst k
    exact T7AggregateParent68.all_checked a
  by_cases h69 : k.val = 69
  · have hk : k = 69 := Fin.ext h69
    subst k
    exact T7AggregateParent69.all_checked a
  by_cases h70 : k.val = 70
  · have hk : k = 70 := Fin.ext h70
    subst k
    exact T7AggregateParent70.all_checked a
  by_cases h71 : k.val = 71
  · have hk : k = 71 := Fin.ext h71
    subst k
    exact T7AggregateParent71.all_checked a
  by_cases h72 : k.val = 72
  · have hk : k = 72 := Fin.ext h72
    subst k
    exact T7AggregateParent72.all_checked a
  by_cases h73 : k.val = 73
  · have hk : k = 73 := Fin.ext h73
    subst k
    exact T7AggregateParent73.all_checked a
  by_cases h74 : k.val = 74
  · have hk : k = 74 := Fin.ext h74
    subst k
    exact T7AggregateParent74.all_checked a
  by_cases h75 : k.val = 75
  · have hk : k = 75 := Fin.ext h75
    subst k
    exact T7AggregateParent75.all_checked a
  by_cases h76 : k.val = 76
  · have hk : k = 76 := Fin.ext h76
    subst k
    exact T7AggregateParent76.all_checked a
  by_cases h77 : k.val = 77
  · have hk : k = 77 := Fin.ext h77
    subst k
    exact T7AggregateParent77.all_checked a
  by_cases h78 : k.val = 78
  · have hk : k = 78 := Fin.ext h78
    subst k
    exact T7AggregateParent78.all_checked a
  by_cases h79 : k.val = 79
  · have hk : k = 79 := Fin.ext h79
    subst k
    exact T7AggregateParent79.all_checked a
  by_cases h80 : k.val = 80
  · have hk : k = 80 := Fin.ext h80
    subst k
    exact T7AggregateParent80.all_checked a
  by_cases h81 : k.val = 81
  · have hk : k = 81 := Fin.ext h81
    subst k
    exact T7AggregateParent81.all_checked a
  by_cases h82 : k.val = 82
  · have hk : k = 82 := Fin.ext h82
    subst k
    exact T7AggregateParent82.all_checked a
  by_cases h83 : k.val = 83
  · have hk : k = 83 := Fin.ext h83
    subst k
    exact T7AggregateParent83.all_checked a
  by_cases h84 : k.val = 84
  · have hk : k = 84 := Fin.ext h84
    subst k
    exact T7AggregateParent84.all_checked a
  by_cases h85 : k.val = 85
  · have hk : k = 85 := Fin.ext h85
    subst k
    exact T7AggregateParent85.all_checked a
  by_cases h86 : k.val = 86
  · have hk : k = 86 := Fin.ext h86
    subst k
    exact T7AggregateParent86.all_checked a
  by_cases h87 : k.val = 87
  · have hk : k = 87 := Fin.ext h87
    subst k
    exact T7AggregateParent87.all_checked a
  by_cases h88 : k.val = 88
  · have hk : k = 88 := Fin.ext h88
    subst k
    exact T7AggregateParent88.all_checked a
  by_cases h89 : k.val = 89
  · have hk : k = 89 := Fin.ext h89
    subst k
    exact T7AggregateParent89.all_checked a
  by_cases h90 : k.val = 90
  · have hk : k = 90 := Fin.ext h90
    subst k
    exact T7AggregateParent90.all_checked a
  by_cases h91 : k.val = 91
  · have hk : k = 91 := Fin.ext h91
    subst k
    exact T7AggregateParent91.all_checked a
  by_cases h92 : k.val = 92
  · have hk : k = 92 := Fin.ext h92
    subst k
    exact T7AggregateParent92.all_checked a
  by_cases h93 : k.val = 93
  · have hk : k = 93 := Fin.ext h93
    subst k
    exact T7AggregateParent93.all_checked a
  by_cases h94 : k.val = 94
  · have hk : k = 94 := Fin.ext h94
    subst k
    exact T7AggregateParent94.all_checked a
  have hk : k = 95 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent95.all_checked a

#print axioms cross_checks_group2
end SparseMonotiles.CarrierHierarchy.T7FullForward
