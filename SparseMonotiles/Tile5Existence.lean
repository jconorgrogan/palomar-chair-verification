module

public import SparseMonotiles.CarrierExistenceKeyed5
public import SparseMonotiles.CarrierExistenceProfiles5
public import SparseMonotiles.ForwardContactCertificates5

@[expose] public section

/-! Actual nonemptiness of the literal unmarked T5 body. Both finite forward
and profile packages are discharged by checked imports; no existence, world,
exhaustion, body-gluing, or profile premise remains. -/
namespace SparseMonotiles
open CarrierHierarchy CarrierHierarchy.Existence

theorem T5_hasTiling : HasTiling T5 :=
  Catalog5World.hasTiling_of_rules t5_forward_rules (complementaryProfiles5 Catalog5World.facets)

#print axioms T5_hasTiling
end SparseMonotiles
