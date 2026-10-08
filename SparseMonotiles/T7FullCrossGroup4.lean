module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents128–159; all128 roots and every generated role. -/
theorem cross_checks_group4 (k : Fin 408) (hl : 128 ≤ k.val) (hu : k.val < 160)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h128 : k.val = 128
  · have hk : k = 128 := Fin.ext h128
    subst k
    exact T7AggregateParent128.all_checked a
  by_cases h129 : k.val = 129
  · have hk : k = 129 := Fin.ext h129
    subst k
    exact T7AggregateParent129.all_checked a
  by_cases h130 : k.val = 130
  · have hk : k = 130 := Fin.ext h130
    subst k
    exact T7AggregateParent130.all_checked a
  by_cases h131 : k.val = 131
  · have hk : k = 131 := Fin.ext h131
    subst k
    exact T7AggregateParent131.all_checked a
  by_cases h132 : k.val = 132
  · have hk : k = 132 := Fin.ext h132
    subst k
    exact T7AggregateParent132.all_checked a
  by_cases h133 : k.val = 133
  · have hk : k = 133 := Fin.ext h133
    subst k
    exact T7AggregateParent133.all_checked a
  by_cases h134 : k.val = 134
  · have hk : k = 134 := Fin.ext h134
    subst k
    exact T7AggregateParent134.all_checked a
  by_cases h135 : k.val = 135
  · have hk : k = 135 := Fin.ext h135
    subst k
    exact T7AggregateParent135.all_checked a
  by_cases h136 : k.val = 136
  · have hk : k = 136 := Fin.ext h136
    subst k
    exact T7AggregateParent136.all_checked a
  by_cases h137 : k.val = 137
  · have hk : k = 137 := Fin.ext h137
    subst k
    exact T7AggregateParent137.all_checked a
  by_cases h138 : k.val = 138
  · have hk : k = 138 := Fin.ext h138
    subst k
    exact T7AggregateParent138.all_checked a
  by_cases h139 : k.val = 139
  · have hk : k = 139 := Fin.ext h139
    subst k
    exact T7AggregateParent139.all_checked a
  by_cases h140 : k.val = 140
  · have hk : k = 140 := Fin.ext h140
    subst k
    exact T7AggregateParent140.all_checked a
  by_cases h141 : k.val = 141
  · have hk : k = 141 := Fin.ext h141
    subst k
    exact T7AggregateParent141.all_checked a
  by_cases h142 : k.val = 142
  · have hk : k = 142 := Fin.ext h142
    subst k
    exact T7AggregateParent142.all_checked a
  by_cases h143 : k.val = 143
  · have hk : k = 143 := Fin.ext h143
    subst k
    exact T7AggregateParent143.all_checked a
  by_cases h144 : k.val = 144
  · have hk : k = 144 := Fin.ext h144
    subst k
    exact T7AggregateParent144.all_checked a
  by_cases h145 : k.val = 145
  · have hk : k = 145 := Fin.ext h145
    subst k
    exact T7AggregateParent145.all_checked a
  by_cases h146 : k.val = 146
  · have hk : k = 146 := Fin.ext h146
    subst k
    exact T7AggregateParent146.all_checked a
  by_cases h147 : k.val = 147
  · have hk : k = 147 := Fin.ext h147
    subst k
    exact T7AggregateParent147.all_checked a
  by_cases h148 : k.val = 148
  · have hk : k = 148 := Fin.ext h148
    subst k
    exact T7AggregateParent148.all_checked a
  by_cases h149 : k.val = 149
  · have hk : k = 149 := Fin.ext h149
    subst k
    exact T7AggregateParent149.all_checked a
  by_cases h150 : k.val = 150
  · have hk : k = 150 := Fin.ext h150
    subst k
    exact T7AggregateParent150.all_checked a
  by_cases h151 : k.val = 151
  · have hk : k = 151 := Fin.ext h151
    subst k
    exact T7AggregateParent151.all_checked a
  by_cases h152 : k.val = 152
  · have hk : k = 152 := Fin.ext h152
    subst k
    exact T7AggregateParent152.all_checked a
  by_cases h153 : k.val = 153
  · have hk : k = 153 := Fin.ext h153
    subst k
    exact T7AggregateParent153.all_checked a
  by_cases h154 : k.val = 154
  · have hk : k = 154 := Fin.ext h154
    subst k
    exact T7AggregateParent154.all_checked a
  by_cases h155 : k.val = 155
  · have hk : k = 155 := Fin.ext h155
    subst k
    exact T7AggregateParent155.all_checked a
  by_cases h156 : k.val = 156
  · have hk : k = 156 := Fin.ext h156
    subst k
    exact T7AggregateParent156.all_checked a
  by_cases h157 : k.val = 157
  · have hk : k = 157 := Fin.ext h157
    subst k
    exact T7AggregateParent157.all_checked a
  by_cases h158 : k.val = 158
  · have hk : k = 158 := Fin.ext h158
    subst k
    exact T7AggregateParent158.all_checked a
  have hk : k = 159 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent159.all_checked a

#print axioms cross_checks_group4
end SparseMonotiles.CarrierHierarchy.T7FullForward
