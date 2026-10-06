module

public import SparseMonotiles.CarrierExistenceProfiles5Core
public import SparseMonotiles.AtlasReverse5

@[expose] public section

/-! The exact literal reverse-atlas certificate discharges the final finite
profile binding. The resulting ComplementaryProfiles theorem has no premises. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact

theorem complementaryProfiles5 (A : KeyFacetAssignment keys5) :
    ComplementaryProfiles A M5 :=
  complementaryProfiles5_of_literal_binding Canonical.everyAtlas5Key_isLiteral A

#print axioms complementaryProfiles5
end SparseMonotiles.CarrierHierarchy.Existence
