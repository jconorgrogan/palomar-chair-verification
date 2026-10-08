module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents256–287; all128 roots and every generated role. -/
theorem cross_checks_group8 (k : Fin 408) (hl : 256 ≤ k.val) (hu : k.val < 288)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h256 : k.val = 256
  · have hk : k = 256 := Fin.ext h256
    subst k
    exact T7AggregateParent256.all_checked a
  by_cases h257 : k.val = 257
  · have hk : k = 257 := Fin.ext h257
    subst k
    exact T7AggregateParent257.all_checked a
  by_cases h258 : k.val = 258
  · have hk : k = 258 := Fin.ext h258
    subst k
    exact T7AggregateParent258.all_checked a
  by_cases h259 : k.val = 259
  · have hk : k = 259 := Fin.ext h259
    subst k
    exact T7AggregateParent259.all_checked a
  by_cases h260 : k.val = 260
  · have hk : k = 260 := Fin.ext h260
    subst k
    exact T7AggregateParent260.all_checked a
  by_cases h261 : k.val = 261
  · have hk : k = 261 := Fin.ext h261
    subst k
    exact T7AggregateParent261.all_checked a
  by_cases h262 : k.val = 262
  · have hk : k = 262 := Fin.ext h262
    subst k
    exact T7AggregateParent262.all_checked a
  by_cases h263 : k.val = 263
  · have hk : k = 263 := Fin.ext h263
    subst k
    exact T7AggregateParent263.all_checked a
  by_cases h264 : k.val = 264
  · have hk : k = 264 := Fin.ext h264
    subst k
    exact T7AggregateParent264.all_checked a
  by_cases h265 : k.val = 265
  · have hk : k = 265 := Fin.ext h265
    subst k
    exact T7AggregateParent265.all_checked a
  by_cases h266 : k.val = 266
  · have hk : k = 266 := Fin.ext h266
    subst k
    exact T7AggregateParent266.all_checked a
  by_cases h267 : k.val = 267
  · have hk : k = 267 := Fin.ext h267
    subst k
    exact T7AggregateParent267.all_checked a
  by_cases h268 : k.val = 268
  · have hk : k = 268 := Fin.ext h268
    subst k
    exact T7AggregateParent268.all_checked a
  by_cases h269 : k.val = 269
  · have hk : k = 269 := Fin.ext h269
    subst k
    exact T7AggregateParent269.all_checked a
  by_cases h270 : k.val = 270
  · have hk : k = 270 := Fin.ext h270
    subst k
    exact T7AggregateParent270.all_checked a
  by_cases h271 : k.val = 271
  · have hk : k = 271 := Fin.ext h271
    subst k
    exact T7AggregateParent271.all_checked a
  by_cases h272 : k.val = 272
  · have hk : k = 272 := Fin.ext h272
    subst k
    exact T7AggregateParent272.all_checked a
  by_cases h273 : k.val = 273
  · have hk : k = 273 := Fin.ext h273
    subst k
    exact T7AggregateParent273.all_checked a
  by_cases h274 : k.val = 274
  · have hk : k = 274 := Fin.ext h274
    subst k
    exact T7AggregateParent274.all_checked a
  by_cases h275 : k.val = 275
  · have hk : k = 275 := Fin.ext h275
    subst k
    exact T7AggregateParent275.all_checked a
  by_cases h276 : k.val = 276
  · have hk : k = 276 := Fin.ext h276
    subst k
    exact T7AggregateParent276.all_checked a
  by_cases h277 : k.val = 277
  · have hk : k = 277 := Fin.ext h277
    subst k
    exact T7AggregateParent277.all_checked a
  by_cases h278 : k.val = 278
  · have hk : k = 278 := Fin.ext h278
    subst k
    exact T7AggregateParent278.all_checked a
  by_cases h279 : k.val = 279
  · have hk : k = 279 := Fin.ext h279
    subst k
    exact T7AggregateParent279.all_checked a
  by_cases h280 : k.val = 280
  · have hk : k = 280 := Fin.ext h280
    subst k
    exact T7AggregateParent280.all_checked a
  by_cases h281 : k.val = 281
  · have hk : k = 281 := Fin.ext h281
    subst k
    exact T7AggregateParent281.all_checked a
  by_cases h282 : k.val = 282
  · have hk : k = 282 := Fin.ext h282
    subst k
    exact T7AggregateParent282.all_checked a
  by_cases h283 : k.val = 283
  · have hk : k = 283 := Fin.ext h283
    subst k
    exact T7AggregateParent283.all_checked a
  by_cases h284 : k.val = 284
  · have hk : k = 284 := Fin.ext h284
    subst k
    exact T7AggregateParent284.all_checked a
  by_cases h285 : k.val = 285
  · have hk : k = 285 := Fin.ext h285
    subst k
    exact T7AggregateParent285.all_checked a
  by_cases h286 : k.val = 286
  · have hk : k = 286 := Fin.ext h286
    subst k
    exact T7AggregateParent286.all_checked a
  have hk : k = 287 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent287.all_checked a

#print axioms cross_checks_group8
end SparseMonotiles.CarrierHierarchy.T7FullForward
