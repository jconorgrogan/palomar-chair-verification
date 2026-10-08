module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents32–63; all128 roots and every generated role. -/
theorem cross_checks_group1 (k : Fin 408) (hl : 32 ≤ k.val) (hu : k.val < 64)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h32 : k.val = 32
  · have hk : k = 32 := Fin.ext h32
    subst k
    exact T7AggregateParent32.all_checked a
  by_cases h33 : k.val = 33
  · have hk : k = 33 := Fin.ext h33
    subst k
    exact T7AggregateParent33.all_checked a
  by_cases h34 : k.val = 34
  · have hk : k = 34 := Fin.ext h34
    subst k
    exact T7AggregateParent34.all_checked a
  by_cases h35 : k.val = 35
  · have hk : k = 35 := Fin.ext h35
    subst k
    exact T7AggregateParent35.all_checked a
  by_cases h36 : k.val = 36
  · have hk : k = 36 := Fin.ext h36
    subst k
    exact T7AggregateParent36.all_checked a
  by_cases h37 : k.val = 37
  · have hk : k = 37 := Fin.ext h37
    subst k
    exact T7AggregateParent37.all_checked a
  by_cases h38 : k.val = 38
  · have hk : k = 38 := Fin.ext h38
    subst k
    exact T7AggregateParent38.all_checked a
  by_cases h39 : k.val = 39
  · have hk : k = 39 := Fin.ext h39
    subst k
    exact T7AggregateParent39.all_checked a
  by_cases h40 : k.val = 40
  · have hk : k = 40 := Fin.ext h40
    subst k
    exact T7AggregateParent40.all_checked a
  by_cases h41 : k.val = 41
  · have hk : k = 41 := Fin.ext h41
    subst k
    exact T7AggregateParent41.all_checked a
  by_cases h42 : k.val = 42
  · have hk : k = 42 := Fin.ext h42
    subst k
    exact T7AggregateParent42.all_checked a
  by_cases h43 : k.val = 43
  · have hk : k = 43 := Fin.ext h43
    subst k
    exact T7AggregateParent43.all_checked a
  by_cases h44 : k.val = 44
  · have hk : k = 44 := Fin.ext h44
    subst k
    exact T7AggregateParent44.all_checked a
  by_cases h45 : k.val = 45
  · have hk : k = 45 := Fin.ext h45
    subst k
    exact T7AggregateParent45.all_checked a
  by_cases h46 : k.val = 46
  · have hk : k = 46 := Fin.ext h46
    subst k
    exact T7AggregateParent46.all_checked a
  by_cases h47 : k.val = 47
  · have hk : k = 47 := Fin.ext h47
    subst k
    exact T7AggregateParent47.all_checked a
  by_cases h48 : k.val = 48
  · have hk : k = 48 := Fin.ext h48
    subst k
    exact T7AggregateParent48.all_checked a
  by_cases h49 : k.val = 49
  · have hk : k = 49 := Fin.ext h49
    subst k
    exact T7AggregateParent49.all_checked a
  by_cases h50 : k.val = 50
  · have hk : k = 50 := Fin.ext h50
    subst k
    exact T7AggregateParent50.all_checked a
  by_cases h51 : k.val = 51
  · have hk : k = 51 := Fin.ext h51
    subst k
    exact T7AggregateParent51.all_checked a
  by_cases h52 : k.val = 52
  · have hk : k = 52 := Fin.ext h52
    subst k
    exact T7AggregateParent52.all_checked a
  by_cases h53 : k.val = 53
  · have hk : k = 53 := Fin.ext h53
    subst k
    exact T7AggregateParent53.all_checked a
  by_cases h54 : k.val = 54
  · have hk : k = 54 := Fin.ext h54
    subst k
    exact T7AggregateParent54.all_checked a
  by_cases h55 : k.val = 55
  · have hk : k = 55 := Fin.ext h55
    subst k
    exact T7AggregateParent55.all_checked a
  by_cases h56 : k.val = 56
  · have hk : k = 56 := Fin.ext h56
    subst k
    exact T7AggregateParent56.all_checked a
  by_cases h57 : k.val = 57
  · have hk : k = 57 := Fin.ext h57
    subst k
    exact T7AggregateParent57.all_checked a
  by_cases h58 : k.val = 58
  · have hk : k = 58 := Fin.ext h58
    subst k
    exact T7AggregateParent58.all_checked a
  by_cases h59 : k.val = 59
  · have hk : k = 59 := Fin.ext h59
    subst k
    exact T7AggregateParent59.all_checked a
  by_cases h60 : k.val = 60
  · have hk : k = 60 := Fin.ext h60
    subst k
    exact T7AggregateParent60.all_checked a
  by_cases h61 : k.val = 61
  · have hk : k = 61 := Fin.ext h61
    subst k
    exact T7AggregateParent61.all_checked a
  by_cases h62 : k.val = 62
  · have hk : k = 62 := Fin.ext h62
    subst k
    exact T7AggregateParent62.all_checked a
  have hk : k = 63 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent63.all_checked a

#print axioms cross_checks_group1
end SparseMonotiles.CarrierHierarchy.T7FullForward
