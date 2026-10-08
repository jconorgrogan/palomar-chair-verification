module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents384–407; all128 roots and every generated role. -/
theorem cross_checks_group12 (k : Fin 408) (hl : 384 ≤ k.val) (hu : k.val < 408)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h384 : k.val = 384
  · have hk : k = 384 := Fin.ext h384
    subst k
    exact T7AggregateParent384.all_checked a
  by_cases h385 : k.val = 385
  · have hk : k = 385 := Fin.ext h385
    subst k
    exact T7AggregateParent385.all_checked a
  by_cases h386 : k.val = 386
  · have hk : k = 386 := Fin.ext h386
    subst k
    exact T7AggregateParent386.all_checked a
  by_cases h387 : k.val = 387
  · have hk : k = 387 := Fin.ext h387
    subst k
    exact T7AggregateParent387.all_checked a
  by_cases h388 : k.val = 388
  · have hk : k = 388 := Fin.ext h388
    subst k
    exact T7AggregateParent388.all_checked a
  by_cases h389 : k.val = 389
  · have hk : k = 389 := Fin.ext h389
    subst k
    exact T7AggregateParent389.all_checked a
  by_cases h390 : k.val = 390
  · have hk : k = 390 := Fin.ext h390
    subst k
    exact T7AggregateParent390.all_checked a
  by_cases h391 : k.val = 391
  · have hk : k = 391 := Fin.ext h391
    subst k
    exact T7AggregateParent391.all_checked a
  by_cases h392 : k.val = 392
  · have hk : k = 392 := Fin.ext h392
    subst k
    exact T7AggregateParent392.all_checked a
  by_cases h393 : k.val = 393
  · have hk : k = 393 := Fin.ext h393
    subst k
    exact T7AggregateParent393.all_checked a
  by_cases h394 : k.val = 394
  · have hk : k = 394 := Fin.ext h394
    subst k
    exact T7AggregateParent394.all_checked a
  by_cases h395 : k.val = 395
  · have hk : k = 395 := Fin.ext h395
    subst k
    exact T7AggregateParent395.all_checked a
  by_cases h396 : k.val = 396
  · have hk : k = 396 := Fin.ext h396
    subst k
    exact T7AggregateParent396.all_checked a
  by_cases h397 : k.val = 397
  · have hk : k = 397 := Fin.ext h397
    subst k
    exact T7AggregateParent397.all_checked a
  by_cases h398 : k.val = 398
  · have hk : k = 398 := Fin.ext h398
    subst k
    exact T7AggregateParent398.all_checked a
  by_cases h399 : k.val = 399
  · have hk : k = 399 := Fin.ext h399
    subst k
    exact T7AggregateParent399.all_checked a
  by_cases h400 : k.val = 400
  · have hk : k = 400 := Fin.ext h400
    subst k
    exact T7AggregateParent400.all_checked a
  by_cases h401 : k.val = 401
  · have hk : k = 401 := Fin.ext h401
    subst k
    exact T7AggregateParent401.all_checked a
  by_cases h402 : k.val = 402
  · have hk : k = 402 := Fin.ext h402
    subst k
    exact T7AggregateParent402.all_checked a
  by_cases h403 : k.val = 403
  · have hk : k = 403 := Fin.ext h403
    subst k
    exact T7AggregateParent403.all_checked a
  by_cases h404 : k.val = 404
  · have hk : k = 404 := Fin.ext h404
    subst k
    exact T7AggregateParent404.all_checked a
  by_cases h405 : k.val = 405
  · have hk : k = 405 := Fin.ext h405
    subst k
    exact T7AggregateParent405.all_checked a
  by_cases h406 : k.val = 406
  · have hk : k = 406 := Fin.ext h406
    subst k
    exact T7AggregateParent406.all_checked a
  have hk : k = 407 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent407.all_checked a

#print axioms cross_checks_group12
end SparseMonotiles.CarrierHierarchy.T7FullForward
