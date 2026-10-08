module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents0–31; all128 roots and every generated role. -/
theorem cross_checks_group0 (k : Fin 408) (hl : 0 ≤ k.val) (hu : k.val < 32)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h0 : k.val = 0
  · have hk : k = 0 := Fin.ext h0
    subst k
    exact T7AggregateParent0.all_checked a
  by_cases h1 : k.val = 1
  · have hk : k = 1 := Fin.ext h1
    subst k
    exact T7AggregateParent1.all_checked a
  by_cases h2 : k.val = 2
  · have hk : k = 2 := Fin.ext h2
    subst k
    exact T7AggregateParent2.all_checked a
  by_cases h3 : k.val = 3
  · have hk : k = 3 := Fin.ext h3
    subst k
    exact T7AggregateParent3.all_checked a
  by_cases h4 : k.val = 4
  · have hk : k = 4 := Fin.ext h4
    subst k
    exact T7AggregateParent4.all_checked a
  by_cases h5 : k.val = 5
  · have hk : k = 5 := Fin.ext h5
    subst k
    exact T7AggregateParent5.all_checked a
  by_cases h6 : k.val = 6
  · have hk : k = 6 := Fin.ext h6
    subst k
    exact T7AggregateParent6.all_checked a
  by_cases h7 : k.val = 7
  · have hk : k = 7 := Fin.ext h7
    subst k
    exact T7AggregateParent7.all_checked a
  by_cases h8 : k.val = 8
  · have hk : k = 8 := Fin.ext h8
    subst k
    exact T7AggregateParent8.all_checked a
  by_cases h9 : k.val = 9
  · have hk : k = 9 := Fin.ext h9
    subst k
    exact T7AggregateParent9.all_checked a
  by_cases h10 : k.val = 10
  · have hk : k = 10 := Fin.ext h10
    subst k
    exact T7AggregateParent10.all_checked a
  by_cases h11 : k.val = 11
  · have hk : k = 11 := Fin.ext h11
    subst k
    exact T7AggregateParent11.all_checked a
  by_cases h12 : k.val = 12
  · have hk : k = 12 := Fin.ext h12
    subst k
    exact T7AggregateParent12.all_checked a
  by_cases h13 : k.val = 13
  · have hk : k = 13 := Fin.ext h13
    subst k
    exact T7AggregateParent13.all_checked a
  by_cases h14 : k.val = 14
  · have hk : k = 14 := Fin.ext h14
    subst k
    exact T7AggregateParent14.all_checked a
  by_cases h15 : k.val = 15
  · have hk : k = 15 := Fin.ext h15
    subst k
    exact T7AggregateParent15.all_checked a
  by_cases h16 : k.val = 16
  · have hk : k = 16 := Fin.ext h16
    subst k
    exact T7AggregateParent16.all_checked a
  by_cases h17 : k.val = 17
  · have hk : k = 17 := Fin.ext h17
    subst k
    exact T7AggregateParent17.all_checked a
  by_cases h18 : k.val = 18
  · have hk : k = 18 := Fin.ext h18
    subst k
    exact T7AggregateParent18.all_checked a
  by_cases h19 : k.val = 19
  · have hk : k = 19 := Fin.ext h19
    subst k
    exact T7AggregateParent19.all_checked a
  by_cases h20 : k.val = 20
  · have hk : k = 20 := Fin.ext h20
    subst k
    exact T7AggregateParent20.all_checked a
  by_cases h21 : k.val = 21
  · have hk : k = 21 := Fin.ext h21
    subst k
    exact T7AggregateParent21.all_checked a
  by_cases h22 : k.val = 22
  · have hk : k = 22 := Fin.ext h22
    subst k
    exact T7AggregateParent22.all_checked a
  by_cases h23 : k.val = 23
  · have hk : k = 23 := Fin.ext h23
    subst k
    exact T7AggregateParent23.all_checked a
  by_cases h24 : k.val = 24
  · have hk : k = 24 := Fin.ext h24
    subst k
    exact T7AggregateParent24.all_checked a
  by_cases h25 : k.val = 25
  · have hk : k = 25 := Fin.ext h25
    subst k
    exact T7AggregateParent25.all_checked a
  by_cases h26 : k.val = 26
  · have hk : k = 26 := Fin.ext h26
    subst k
    exact T7AggregateParent26.all_checked a
  by_cases h27 : k.val = 27
  · have hk : k = 27 := Fin.ext h27
    subst k
    exact T7AggregateParent27.all_checked a
  by_cases h28 : k.val = 28
  · have hk : k = 28 := Fin.ext h28
    subst k
    exact T7AggregateParent28.all_checked a
  by_cases h29 : k.val = 29
  · have hk : k = 29 := Fin.ext h29
    subst k
    exact T7AggregateParent29.all_checked a
  by_cases h30 : k.val = 30
  · have hk : k = 30 := Fin.ext h30
    subst k
    exact T7AggregateParent30.all_checked a
  have hk : k = 31 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent31.all_checked a

#print axioms cross_checks_group0
end SparseMonotiles.CarrierHierarchy.T7FullForward
