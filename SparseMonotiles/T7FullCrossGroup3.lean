module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents96–127; all128 roots and every generated role. -/
theorem cross_checks_group3 (k : Fin 408) (hl : 96 ≤ k.val) (hu : k.val < 128)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h96 : k.val = 96
  · have hk : k = 96 := Fin.ext h96
    subst k
    exact T7AggregateParent96.all_checked a
  by_cases h97 : k.val = 97
  · have hk : k = 97 := Fin.ext h97
    subst k
    exact T7AggregateParent97.all_checked a
  by_cases h98 : k.val = 98
  · have hk : k = 98 := Fin.ext h98
    subst k
    exact T7AggregateParent98.all_checked a
  by_cases h99 : k.val = 99
  · have hk : k = 99 := Fin.ext h99
    subst k
    exact T7AggregateParent99.all_checked a
  by_cases h100 : k.val = 100
  · have hk : k = 100 := Fin.ext h100
    subst k
    exact T7AggregateParent100.all_checked a
  by_cases h101 : k.val = 101
  · have hk : k = 101 := Fin.ext h101
    subst k
    exact T7AggregateParent101.all_checked a
  by_cases h102 : k.val = 102
  · have hk : k = 102 := Fin.ext h102
    subst k
    exact T7AggregateParent102.all_checked a
  by_cases h103 : k.val = 103
  · have hk : k = 103 := Fin.ext h103
    subst k
    exact T7AggregateParent103.all_checked a
  by_cases h104 : k.val = 104
  · have hk : k = 104 := Fin.ext h104
    subst k
    exact T7AggregateParent104.all_checked a
  by_cases h105 : k.val = 105
  · have hk : k = 105 := Fin.ext h105
    subst k
    exact T7AggregateParent105.all_checked a
  by_cases h106 : k.val = 106
  · have hk : k = 106 := Fin.ext h106
    subst k
    exact T7AggregateParent106.all_checked a
  by_cases h107 : k.val = 107
  · have hk : k = 107 := Fin.ext h107
    subst k
    exact T7AggregateParent107.all_checked a
  by_cases h108 : k.val = 108
  · have hk : k = 108 := Fin.ext h108
    subst k
    exact T7AggregateParent108.all_checked a
  by_cases h109 : k.val = 109
  · have hk : k = 109 := Fin.ext h109
    subst k
    exact T7AggregateParent109.all_checked a
  by_cases h110 : k.val = 110
  · have hk : k = 110 := Fin.ext h110
    subst k
    exact T7AggregateParent110.all_checked a
  by_cases h111 : k.val = 111
  · have hk : k = 111 := Fin.ext h111
    subst k
    exact T7AggregateParent111.all_checked a
  by_cases h112 : k.val = 112
  · have hk : k = 112 := Fin.ext h112
    subst k
    exact T7AggregateParent112.all_checked a
  by_cases h113 : k.val = 113
  · have hk : k = 113 := Fin.ext h113
    subst k
    exact T7AggregateParent113.all_checked a
  by_cases h114 : k.val = 114
  · have hk : k = 114 := Fin.ext h114
    subst k
    exact T7AggregateParent114.all_checked a
  by_cases h115 : k.val = 115
  · have hk : k = 115 := Fin.ext h115
    subst k
    exact T7AggregateParent115.all_checked a
  by_cases h116 : k.val = 116
  · have hk : k = 116 := Fin.ext h116
    subst k
    exact T7AggregateParent116.all_checked a
  by_cases h117 : k.val = 117
  · have hk : k = 117 := Fin.ext h117
    subst k
    exact T7AggregateParent117.all_checked a
  by_cases h118 : k.val = 118
  · have hk : k = 118 := Fin.ext h118
    subst k
    exact T7AggregateParent118.all_checked a
  by_cases h119 : k.val = 119
  · have hk : k = 119 := Fin.ext h119
    subst k
    exact T7AggregateParent119.all_checked a
  by_cases h120 : k.val = 120
  · have hk : k = 120 := Fin.ext h120
    subst k
    exact T7AggregateParent120.all_checked a
  by_cases h121 : k.val = 121
  · have hk : k = 121 := Fin.ext h121
    subst k
    exact T7AggregateParent121.all_checked a
  by_cases h122 : k.val = 122
  · have hk : k = 122 := Fin.ext h122
    subst k
    exact T7AggregateParent122.all_checked a
  by_cases h123 : k.val = 123
  · have hk : k = 123 := Fin.ext h123
    subst k
    exact T7AggregateParent123.all_checked a
  by_cases h124 : k.val = 124
  · have hk : k = 124 := Fin.ext h124
    subst k
    exact T7AggregateParent124.all_checked a
  by_cases h125 : k.val = 125
  · have hk : k = 125 := Fin.ext h125
    subst k
    exact T7AggregateParent125.all_checked a
  by_cases h126 : k.val = 126
  · have hk : k = 126 := Fin.ext h126
    subst k
    exact T7AggregateParent126.all_checked a
  have hk : k = 127 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent127.all_checked a

#print axioms cross_checks_group3
end SparseMonotiles.CarrierHierarchy.T7FullForward
