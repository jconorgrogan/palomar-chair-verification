module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents224–255; all128 roots and every generated role. -/
theorem cross_checks_group7 (k : Fin 408) (hl : 224 ≤ k.val) (hu : k.val < 256)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h224 : k.val = 224
  · have hk : k = 224 := Fin.ext h224
    subst k
    exact T7AggregateParent224.all_checked a
  by_cases h225 : k.val = 225
  · have hk : k = 225 := Fin.ext h225
    subst k
    exact T7AggregateParent225.all_checked a
  by_cases h226 : k.val = 226
  · have hk : k = 226 := Fin.ext h226
    subst k
    exact T7AggregateParent226.all_checked a
  by_cases h227 : k.val = 227
  · have hk : k = 227 := Fin.ext h227
    subst k
    exact T7AggregateParent227.all_checked a
  by_cases h228 : k.val = 228
  · have hk : k = 228 := Fin.ext h228
    subst k
    exact T7AggregateParent228.all_checked a
  by_cases h229 : k.val = 229
  · have hk : k = 229 := Fin.ext h229
    subst k
    exact T7AggregateParent229.all_checked a
  by_cases h230 : k.val = 230
  · have hk : k = 230 := Fin.ext h230
    subst k
    exact T7AggregateParent230.all_checked a
  by_cases h231 : k.val = 231
  · have hk : k = 231 := Fin.ext h231
    subst k
    exact T7AggregateParent231.all_checked a
  by_cases h232 : k.val = 232
  · have hk : k = 232 := Fin.ext h232
    subst k
    exact T7AggregateParent232.all_checked a
  by_cases h233 : k.val = 233
  · have hk : k = 233 := Fin.ext h233
    subst k
    exact T7AggregateParent233.all_checked a
  by_cases h234 : k.val = 234
  · have hk : k = 234 := Fin.ext h234
    subst k
    exact T7AggregateParent234.all_checked a
  by_cases h235 : k.val = 235
  · have hk : k = 235 := Fin.ext h235
    subst k
    exact T7AggregateParent235.all_checked a
  by_cases h236 : k.val = 236
  · have hk : k = 236 := Fin.ext h236
    subst k
    exact T7AggregateParent236.all_checked a
  by_cases h237 : k.val = 237
  · have hk : k = 237 := Fin.ext h237
    subst k
    exact T7AggregateParent237.all_checked a
  by_cases h238 : k.val = 238
  · have hk : k = 238 := Fin.ext h238
    subst k
    exact T7AggregateParent238.all_checked a
  by_cases h239 : k.val = 239
  · have hk : k = 239 := Fin.ext h239
    subst k
    exact T7AggregateParent239.all_checked a
  by_cases h240 : k.val = 240
  · have hk : k = 240 := Fin.ext h240
    subst k
    exact T7AggregateParent240.all_checked a
  by_cases h241 : k.val = 241
  · have hk : k = 241 := Fin.ext h241
    subst k
    exact T7AggregateParent241.all_checked a
  by_cases h242 : k.val = 242
  · have hk : k = 242 := Fin.ext h242
    subst k
    exact T7AggregateParent242.all_checked a
  by_cases h243 : k.val = 243
  · have hk : k = 243 := Fin.ext h243
    subst k
    exact T7AggregateParent243.all_checked a
  by_cases h244 : k.val = 244
  · have hk : k = 244 := Fin.ext h244
    subst k
    exact T7AggregateParent244.all_checked a
  by_cases h245 : k.val = 245
  · have hk : k = 245 := Fin.ext h245
    subst k
    exact T7AggregateParent245.all_checked a
  by_cases h246 : k.val = 246
  · have hk : k = 246 := Fin.ext h246
    subst k
    exact T7AggregateParent246.all_checked a
  by_cases h247 : k.val = 247
  · have hk : k = 247 := Fin.ext h247
    subst k
    exact T7AggregateParent247.all_checked a
  by_cases h248 : k.val = 248
  · have hk : k = 248 := Fin.ext h248
    subst k
    exact T7AggregateParent248.all_checked a
  by_cases h249 : k.val = 249
  · have hk : k = 249 := Fin.ext h249
    subst k
    exact T7AggregateParent249.all_checked a
  by_cases h250 : k.val = 250
  · have hk : k = 250 := Fin.ext h250
    subst k
    exact T7AggregateParent250.all_checked a
  by_cases h251 : k.val = 251
  · have hk : k = 251 := Fin.ext h251
    subst k
    exact T7AggregateParent251.all_checked a
  by_cases h252 : k.val = 252
  · have hk : k = 252 := Fin.ext h252
    subst k
    exact T7AggregateParent252.all_checked a
  by_cases h253 : k.val = 253
  · have hk : k = 253 := Fin.ext h253
    subst k
    exact T7AggregateParent253.all_checked a
  by_cases h254 : k.val = 254
  · have hk : k = 254 := Fin.ext h254
    subst k
    exact T7AggregateParent254.all_checked a
  have hk : k = 255 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent255.all_checked a

#print axioms cross_checks_group7
end SparseMonotiles.CarrierHierarchy.T7FullForward
