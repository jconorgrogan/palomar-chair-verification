module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents352–383; all128 roots and every generated role. -/
theorem cross_checks_group11 (k : Fin 408) (hl : 352 ≤ k.val) (hu : k.val < 384)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h352 : k.val = 352
  · have hk : k = 352 := Fin.ext h352
    subst k
    exact T7AggregateParent352.all_checked a
  by_cases h353 : k.val = 353
  · have hk : k = 353 := Fin.ext h353
    subst k
    exact T7AggregateParent353.all_checked a
  by_cases h354 : k.val = 354
  · have hk : k = 354 := Fin.ext h354
    subst k
    exact T7AggregateParent354.all_checked a
  by_cases h355 : k.val = 355
  · have hk : k = 355 := Fin.ext h355
    subst k
    exact T7AggregateParent355.all_checked a
  by_cases h356 : k.val = 356
  · have hk : k = 356 := Fin.ext h356
    subst k
    exact T7AggregateParent356.all_checked a
  by_cases h357 : k.val = 357
  · have hk : k = 357 := Fin.ext h357
    subst k
    exact T7AggregateParent357.all_checked a
  by_cases h358 : k.val = 358
  · have hk : k = 358 := Fin.ext h358
    subst k
    exact T7AggregateParent358.all_checked a
  by_cases h359 : k.val = 359
  · have hk : k = 359 := Fin.ext h359
    subst k
    exact T7AggregateParent359.all_checked a
  by_cases h360 : k.val = 360
  · have hk : k = 360 := Fin.ext h360
    subst k
    exact T7AggregateParent360.all_checked a
  by_cases h361 : k.val = 361
  · have hk : k = 361 := Fin.ext h361
    subst k
    exact T7AggregateParent361.all_checked a
  by_cases h362 : k.val = 362
  · have hk : k = 362 := Fin.ext h362
    subst k
    exact T7AggregateParent362.all_checked a
  by_cases h363 : k.val = 363
  · have hk : k = 363 := Fin.ext h363
    subst k
    exact T7AggregateParent363.all_checked a
  by_cases h364 : k.val = 364
  · have hk : k = 364 := Fin.ext h364
    subst k
    exact T7AggregateParent364.all_checked a
  by_cases h365 : k.val = 365
  · have hk : k = 365 := Fin.ext h365
    subst k
    exact T7AggregateParent365.all_checked a
  by_cases h366 : k.val = 366
  · have hk : k = 366 := Fin.ext h366
    subst k
    exact T7AggregateParent366.all_checked a
  by_cases h367 : k.val = 367
  · have hk : k = 367 := Fin.ext h367
    subst k
    exact T7AggregateParent367.all_checked a
  by_cases h368 : k.val = 368
  · have hk : k = 368 := Fin.ext h368
    subst k
    exact T7AggregateParent368.all_checked a
  by_cases h369 : k.val = 369
  · have hk : k = 369 := Fin.ext h369
    subst k
    exact T7AggregateParent369.all_checked a
  by_cases h370 : k.val = 370
  · have hk : k = 370 := Fin.ext h370
    subst k
    exact T7AggregateParent370.all_checked a
  by_cases h371 : k.val = 371
  · have hk : k = 371 := Fin.ext h371
    subst k
    exact T7AggregateParent371.all_checked a
  by_cases h372 : k.val = 372
  · have hk : k = 372 := Fin.ext h372
    subst k
    exact T7AggregateParent372.all_checked a
  by_cases h373 : k.val = 373
  · have hk : k = 373 := Fin.ext h373
    subst k
    exact T7AggregateParent373.all_checked a
  by_cases h374 : k.val = 374
  · have hk : k = 374 := Fin.ext h374
    subst k
    exact T7AggregateParent374.all_checked a
  by_cases h375 : k.val = 375
  · have hk : k = 375 := Fin.ext h375
    subst k
    exact T7AggregateParent375.all_checked a
  by_cases h376 : k.val = 376
  · have hk : k = 376 := Fin.ext h376
    subst k
    exact T7AggregateParent376.all_checked a
  by_cases h377 : k.val = 377
  · have hk : k = 377 := Fin.ext h377
    subst k
    exact T7AggregateParent377.all_checked a
  by_cases h378 : k.val = 378
  · have hk : k = 378 := Fin.ext h378
    subst k
    exact T7AggregateParent378.all_checked a
  by_cases h379 : k.val = 379
  · have hk : k = 379 := Fin.ext h379
    subst k
    exact T7AggregateParent379.all_checked a
  by_cases h380 : k.val = 380
  · have hk : k = 380 := Fin.ext h380
    subst k
    exact T7AggregateParent380.all_checked a
  by_cases h381 : k.val = 381
  · have hk : k = 381 := Fin.ext h381
    subst k
    exact T7AggregateParent381.all_checked a
  by_cases h382 : k.val = 382
  · have hk : k = 382 := Fin.ext h382
    subst k
    exact T7AggregateParent382.all_checked a
  have hk : k = 383 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent383.all_checked a

#print axioms cross_checks_group11
end SparseMonotiles.CarrierHierarchy.T7FullForward
