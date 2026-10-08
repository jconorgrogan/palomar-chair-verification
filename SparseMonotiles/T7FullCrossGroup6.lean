module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents192–223; all128 roots and every generated role. -/
theorem cross_checks_group6 (k : Fin 408) (hl : 192 ≤ k.val) (hu : k.val < 224)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h192 : k.val = 192
  · have hk : k = 192 := Fin.ext h192
    subst k
    exact T7AggregateParent192.all_checked a
  by_cases h193 : k.val = 193
  · have hk : k = 193 := Fin.ext h193
    subst k
    exact T7AggregateParent193.all_checked a
  by_cases h194 : k.val = 194
  · have hk : k = 194 := Fin.ext h194
    subst k
    exact T7AggregateParent194.all_checked a
  by_cases h195 : k.val = 195
  · have hk : k = 195 := Fin.ext h195
    subst k
    exact T7AggregateParent195.all_checked a
  by_cases h196 : k.val = 196
  · have hk : k = 196 := Fin.ext h196
    subst k
    exact T7AggregateParent196.all_checked a
  by_cases h197 : k.val = 197
  · have hk : k = 197 := Fin.ext h197
    subst k
    exact T7AggregateParent197.all_checked a
  by_cases h198 : k.val = 198
  · have hk : k = 198 := Fin.ext h198
    subst k
    exact T7AggregateParent198.all_checked a
  by_cases h199 : k.val = 199
  · have hk : k = 199 := Fin.ext h199
    subst k
    exact T7AggregateParent199.all_checked a
  by_cases h200 : k.val = 200
  · have hk : k = 200 := Fin.ext h200
    subst k
    exact T7AggregateParent200.all_checked a
  by_cases h201 : k.val = 201
  · have hk : k = 201 := Fin.ext h201
    subst k
    exact T7AggregateParent201.all_checked a
  by_cases h202 : k.val = 202
  · have hk : k = 202 := Fin.ext h202
    subst k
    exact T7AggregateParent202.all_checked a
  by_cases h203 : k.val = 203
  · have hk : k = 203 := Fin.ext h203
    subst k
    exact T7AggregateParent203.all_checked a
  by_cases h204 : k.val = 204
  · have hk : k = 204 := Fin.ext h204
    subst k
    exact T7AggregateParent204.all_checked a
  by_cases h205 : k.val = 205
  · have hk : k = 205 := Fin.ext h205
    subst k
    exact T7AggregateParent205.all_checked a
  by_cases h206 : k.val = 206
  · have hk : k = 206 := Fin.ext h206
    subst k
    exact T7AggregateParent206.all_checked a
  by_cases h207 : k.val = 207
  · have hk : k = 207 := Fin.ext h207
    subst k
    exact T7AggregateParent207.all_checked a
  by_cases h208 : k.val = 208
  · have hk : k = 208 := Fin.ext h208
    subst k
    exact T7AggregateParent208.all_checked a
  by_cases h209 : k.val = 209
  · have hk : k = 209 := Fin.ext h209
    subst k
    exact T7AggregateParent209.all_checked a
  by_cases h210 : k.val = 210
  · have hk : k = 210 := Fin.ext h210
    subst k
    exact T7AggregateParent210.all_checked a
  by_cases h211 : k.val = 211
  · have hk : k = 211 := Fin.ext h211
    subst k
    exact T7AggregateParent211.all_checked a
  by_cases h212 : k.val = 212
  · have hk : k = 212 := Fin.ext h212
    subst k
    exact T7AggregateParent212.all_checked a
  by_cases h213 : k.val = 213
  · have hk : k = 213 := Fin.ext h213
    subst k
    exact T7AggregateParent213.all_checked a
  by_cases h214 : k.val = 214
  · have hk : k = 214 := Fin.ext h214
    subst k
    exact T7AggregateParent214.all_checked a
  by_cases h215 : k.val = 215
  · have hk : k = 215 := Fin.ext h215
    subst k
    exact T7AggregateParent215.all_checked a
  by_cases h216 : k.val = 216
  · have hk : k = 216 := Fin.ext h216
    subst k
    exact T7AggregateParent216.all_checked a
  by_cases h217 : k.val = 217
  · have hk : k = 217 := Fin.ext h217
    subst k
    exact T7AggregateParent217.all_checked a
  by_cases h218 : k.val = 218
  · have hk : k = 218 := Fin.ext h218
    subst k
    exact T7AggregateParent218.all_checked a
  by_cases h219 : k.val = 219
  · have hk : k = 219 := Fin.ext h219
    subst k
    exact T7AggregateParent219.all_checked a
  by_cases h220 : k.val = 220
  · have hk : k = 220 := Fin.ext h220
    subst k
    exact T7AggregateParent220.all_checked a
  by_cases h221 : k.val = 221
  · have hk : k = 221 := Fin.ext h221
    subst k
    exact T7AggregateParent221.all_checked a
  by_cases h222 : k.val = 222
  · have hk : k = 222 := Fin.ext h222
    subst k
    exact T7AggregateParent222.all_checked a
  have hk : k = 223 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent223.all_checked a

#print axioms cross_checks_group6
end SparseMonotiles.CarrierHierarchy.T7FullForward
