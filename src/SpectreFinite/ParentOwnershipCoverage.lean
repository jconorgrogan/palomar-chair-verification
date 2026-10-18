module

public import SpectreFinite.ParentOwnership
public import SpectreFinite.HexRegionGeometry

@[expose] public section


/-! Exact geometric support of the paper's parent assignment. -/
namespace SpectreFinite.HexSearch.ParentOwnership

theorem parent_offsets_radiusTwo :
    ∀ x ∈ primaryOffsets ++ [secondaryOffset], x ∈ hexRegion 2 := by decide

/-- Every backward candidate of a radius-three query is genuinely inside
radius five. This is arithmetic ball inclusion, not a large truth table. -/
theorem radiusThree_candidates_covered :
    ∀ x ∈ hexRegion 3, CoversCandidates (hexRegion 5) x := by
  intro x hx t d hd
  exact subtraction_mem_hexRegion hx
    (hexRegion_rotation 2 t d (parent_offsets_radiusTwo d hd))

/-- Universal conclusion is conditional on occurrence completeness of the
specified family; this module supplies only the geometric support fact. -/
theorem unique_ownership_of_radiusFive_certificate
    (family : List Patch)
    (hcert : ∀ p ∈ family, UniqueAt (patchState p) (0,0))
    (f : Position → State) (hocc : OccurrenceComplete f (hexRegion 5) family) :
    ∀ x : Position, UniqueAt f x :=
  unique_ownership_of_occurrenceComplete (hexRegion 5) family
    (radiusThree_candidates_covered (0,0) (by decide)) hcert f hocc

#print axioms radiusThree_candidates_covered
#print axioms unique_ownership_of_radiusFive_certificate
end SpectreFinite.HexSearch.ParentOwnership
