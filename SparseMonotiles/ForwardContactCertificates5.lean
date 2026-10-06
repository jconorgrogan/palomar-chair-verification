module

public import SparseMonotiles.ForwardContactCertificates5Representatives
public import SparseMonotiles.ForwardContactCertificates5Symmetry

@[expose] public section

/-! Exact finite forward substitution closure of the undecorated T5 carriers.
All 32² sibling source pairs and 284×32² cross-child source triples are covered;
every omitted contact is certified geometrically, independently of coarse necessity.
Physical keyed-body tiling additionally uses complementary profile matching. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

theorem t5_forward_rules : ForwardRules CoarseContactCertificates5.C M5 :=
  ForwardContactCertificates5.forwardRules_of_representatives
    ForwardContactCertificates5.sibling_representatives
    ForwardContactCertificates5.cross_representatives

#print axioms t5_forward_rules
end SparseMonotiles.CarrierHierarchy
