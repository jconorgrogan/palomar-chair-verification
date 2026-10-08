module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents288–319; all128 roots and every generated role. -/
theorem cross_checks_group9 (k : Fin 408) (hl : 288 ≤ k.val) (hu : k.val < 320)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h288 : k.val = 288
  · have hk : k = 288 := Fin.ext h288
    subst k
    exact T7AggregateParent288.all_checked a
  by_cases h289 : k.val = 289
  · have hk : k = 289 := Fin.ext h289
    subst k
    exact T7AggregateParent289.all_checked a
  by_cases h290 : k.val = 290
  · have hk : k = 290 := Fin.ext h290
    subst k
    exact T7AggregateParent290.all_checked a
  by_cases h291 : k.val = 291
  · have hk : k = 291 := Fin.ext h291
    subst k
    exact T7AggregateParent291.all_checked a
  by_cases h292 : k.val = 292
  · have hk : k = 292 := Fin.ext h292
    subst k
    exact T7AggregateParent292.all_checked a
  by_cases h293 : k.val = 293
  · have hk : k = 293 := Fin.ext h293
    subst k
    exact T7AggregateParent293.all_checked a
  by_cases h294 : k.val = 294
  · have hk : k = 294 := Fin.ext h294
    subst k
    exact T7AggregateParent294.all_checked a
  by_cases h295 : k.val = 295
  · have hk : k = 295 := Fin.ext h295
    subst k
    exact T7AggregateParent295.all_checked a
  by_cases h296 : k.val = 296
  · have hk : k = 296 := Fin.ext h296
    subst k
    exact T7AggregateParent296.all_checked a
  by_cases h297 : k.val = 297
  · have hk : k = 297 := Fin.ext h297
    subst k
    exact T7AggregateParent297.all_checked a
  by_cases h298 : k.val = 298
  · have hk : k = 298 := Fin.ext h298
    subst k
    exact T7AggregateParent298.all_checked a
  by_cases h299 : k.val = 299
  · have hk : k = 299 := Fin.ext h299
    subst k
    exact T7AggregateParent299.all_checked a
  by_cases h300 : k.val = 300
  · have hk : k = 300 := Fin.ext h300
    subst k
    exact T7AggregateParent300.all_checked a
  by_cases h301 : k.val = 301
  · have hk : k = 301 := Fin.ext h301
    subst k
    exact T7AggregateParent301.all_checked a
  by_cases h302 : k.val = 302
  · have hk : k = 302 := Fin.ext h302
    subst k
    exact T7AggregateParent302.all_checked a
  by_cases h303 : k.val = 303
  · have hk : k = 303 := Fin.ext h303
    subst k
    exact T7AggregateParent303.all_checked a
  by_cases h304 : k.val = 304
  · have hk : k = 304 := Fin.ext h304
    subst k
    exact T7AggregateParent304.all_checked a
  by_cases h305 : k.val = 305
  · have hk : k = 305 := Fin.ext h305
    subst k
    exact T7AggregateParent305.all_checked a
  by_cases h306 : k.val = 306
  · have hk : k = 306 := Fin.ext h306
    subst k
    exact T7AggregateParent306.all_checked a
  by_cases h307 : k.val = 307
  · have hk : k = 307 := Fin.ext h307
    subst k
    exact T7AggregateParent307.all_checked a
  by_cases h308 : k.val = 308
  · have hk : k = 308 := Fin.ext h308
    subst k
    exact T7AggregateParent308.all_checked a
  by_cases h309 : k.val = 309
  · have hk : k = 309 := Fin.ext h309
    subst k
    exact T7AggregateParent309.all_checked a
  by_cases h310 : k.val = 310
  · have hk : k = 310 := Fin.ext h310
    subst k
    exact T7AggregateParent310.all_checked a
  by_cases h311 : k.val = 311
  · have hk : k = 311 := Fin.ext h311
    subst k
    exact T7AggregateParent311.all_checked a
  by_cases h312 : k.val = 312
  · have hk : k = 312 := Fin.ext h312
    subst k
    exact T7AggregateParent312.all_checked a
  by_cases h313 : k.val = 313
  · have hk : k = 313 := Fin.ext h313
    subst k
    exact T7AggregateParent313.all_checked a
  by_cases h314 : k.val = 314
  · have hk : k = 314 := Fin.ext h314
    subst k
    exact T7AggregateParent314.all_checked a
  by_cases h315 : k.val = 315
  · have hk : k = 315 := Fin.ext h315
    subst k
    exact T7AggregateParent315.all_checked a
  by_cases h316 : k.val = 316
  · have hk : k = 316 := Fin.ext h316
    subst k
    exact T7AggregateParent316.all_checked a
  by_cases h317 : k.val = 317
  · have hk : k = 317 := Fin.ext h317
    subst k
    exact T7AggregateParent317.all_checked a
  by_cases h318 : k.val = 318
  · have hk : k = 318 := Fin.ext h318
    subst k
    exact T7AggregateParent318.all_checked a
  have hk : k = 319 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent319.all_checked a

#print axioms cross_checks_group9
end SparseMonotiles.CarrierHierarchy.T7FullForward
