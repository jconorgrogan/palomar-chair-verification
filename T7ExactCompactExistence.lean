module
public import SparseMonotiles.T7FullForward
public import T7AllM7Acceptance
@[expose] public section
namespace SparseMonotiles.ExactCompactExistence7
open CarrierHierarchy
open CarrierHierarchy.Existence

/-- Actual tiling existence for the literal compact T7 body. This composition
may be checked only after both full finite prerequisite packages have passed. -/
theorem hasTiling : HasTiling T7 :=
  Catalog7World.hasTiling_of_forward_profiles T7FullForward.forward_rules
    ProfileBridge7.Acceptance201.actual_complementaryProfiles

#print axioms hasTiling
#print hasTiling
end SparseMonotiles.ExactCompactExistence7
