module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents320–351; all128 roots and every generated role. -/
theorem cross_checks_group10 (k : Fin 408) (hl : 320 ≤ k.val) (hu : k.val < 352)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h320 : k.val = 320
  · have hk : k = 320 := Fin.ext h320
    subst k
    exact T7AggregateParent320.all_checked a
  by_cases h321 : k.val = 321
  · have hk : k = 321 := Fin.ext h321
    subst k
    exact T7AggregateParent321.all_checked a
  by_cases h322 : k.val = 322
  · have hk : k = 322 := Fin.ext h322
    subst k
    exact T7AggregateParent322.all_checked a
  by_cases h323 : k.val = 323
  · have hk : k = 323 := Fin.ext h323
    subst k
    exact T7AggregateParent323.all_checked a
  by_cases h324 : k.val = 324
  · have hk : k = 324 := Fin.ext h324
    subst k
    exact T7AggregateParent324.all_checked a
  by_cases h325 : k.val = 325
  · have hk : k = 325 := Fin.ext h325
    subst k
    exact T7AggregateParent325.all_checked a
  by_cases h326 : k.val = 326
  · have hk : k = 326 := Fin.ext h326
    subst k
    exact T7AggregateParent326.all_checked a
  by_cases h327 : k.val = 327
  · have hk : k = 327 := Fin.ext h327
    subst k
    exact T7AggregateParent327.all_checked a
  by_cases h328 : k.val = 328
  · have hk : k = 328 := Fin.ext h328
    subst k
    exact T7AggregateParent328.all_checked a
  by_cases h329 : k.val = 329
  · have hk : k = 329 := Fin.ext h329
    subst k
    exact T7AggregateParent329.all_checked a
  by_cases h330 : k.val = 330
  · have hk : k = 330 := Fin.ext h330
    subst k
    exact T7AggregateParent330.all_checked a
  by_cases h331 : k.val = 331
  · have hk : k = 331 := Fin.ext h331
    subst k
    exact T7AggregateParent331.all_checked a
  by_cases h332 : k.val = 332
  · have hk : k = 332 := Fin.ext h332
    subst k
    exact T7AggregateParent332.all_checked a
  by_cases h333 : k.val = 333
  · have hk : k = 333 := Fin.ext h333
    subst k
    exact T7AggregateParent333.all_checked a
  by_cases h334 : k.val = 334
  · have hk : k = 334 := Fin.ext h334
    subst k
    exact T7AggregateParent334.all_checked a
  by_cases h335 : k.val = 335
  · have hk : k = 335 := Fin.ext h335
    subst k
    exact T7AggregateParent335.all_checked a
  by_cases h336 : k.val = 336
  · have hk : k = 336 := Fin.ext h336
    subst k
    exact T7AggregateParent336.all_checked a
  by_cases h337 : k.val = 337
  · have hk : k = 337 := Fin.ext h337
    subst k
    exact T7AggregateParent337.all_checked a
  by_cases h338 : k.val = 338
  · have hk : k = 338 := Fin.ext h338
    subst k
    exact T7AggregateParent338.all_checked a
  by_cases h339 : k.val = 339
  · have hk : k = 339 := Fin.ext h339
    subst k
    exact T7AggregateParent339.all_checked a
  by_cases h340 : k.val = 340
  · have hk : k = 340 := Fin.ext h340
    subst k
    exact T7AggregateParent340.all_checked a
  by_cases h341 : k.val = 341
  · have hk : k = 341 := Fin.ext h341
    subst k
    exact T7AggregateParent341.all_checked a
  by_cases h342 : k.val = 342
  · have hk : k = 342 := Fin.ext h342
    subst k
    exact T7AggregateParent342.all_checked a
  by_cases h343 : k.val = 343
  · have hk : k = 343 := Fin.ext h343
    subst k
    exact T7AggregateParent343.all_checked a
  by_cases h344 : k.val = 344
  · have hk : k = 344 := Fin.ext h344
    subst k
    exact T7AggregateParent344.all_checked a
  by_cases h345 : k.val = 345
  · have hk : k = 345 := Fin.ext h345
    subst k
    exact T7AggregateParent345.all_checked a
  by_cases h346 : k.val = 346
  · have hk : k = 346 := Fin.ext h346
    subst k
    exact T7AggregateParent346.all_checked a
  by_cases h347 : k.val = 347
  · have hk : k = 347 := Fin.ext h347
    subst k
    exact T7AggregateParent347.all_checked a
  by_cases h348 : k.val = 348
  · have hk : k = 348 := Fin.ext h348
    subst k
    exact T7AggregateParent348.all_checked a
  by_cases h349 : k.val = 349
  · have hk : k = 349 := Fin.ext h349
    subst k
    exact T7AggregateParent349.all_checked a
  by_cases h350 : k.val = 350
  · have hk : k = 350 := Fin.ext h350
    subst k
    exact T7AggregateParent350.all_checked a
  have hk : k = 351 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent351.all_checked a

#print axioms cross_checks_group10
end SparseMonotiles.CarrierHierarchy.T7FullForward
