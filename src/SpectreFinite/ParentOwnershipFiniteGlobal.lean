module

public import SpectreFinite.ParentOwnershipFinite
public import SpectreFinite.ParentFramedPatterns

@[expose] public section


/-! Whole-field consequences of the literal finite certificates, explicitly
conditional on occurrence completeness for every globally legal field.
This is not a completeness, parent-boundary, substitution, or tiling theorem. -/
namespace SpectreFinite.HexSearch.ParentOwnership

theorem certifiedFamily_every_cell_has_unique_owner
    (hcomplete : ∀ g : Position → State, GloballyLegal g →
      OccurrenceComplete g (hexRegion 5) certifiedParentFamily)
    (f : Position → State) (hf : GloballyLegal f) :
    ∀ x : Position, ∃ a : Position,
      a ∈ owners f x ∧ ∀ b : Position, b ∈ owners f x → b = a := by
  intro x
  exact uniqueAt_selected f x
    (unique_ownership_of_certifiedParentFamily f (hcomplete f hf) x)

theorem certifiedFamily_every_Gamma_has_exact_framed_parent
    (hcomplete : ∀ g : Position → State, GloballyLegal g →
      OccurrenceComplete g (hexRegion 5) certifiedParentFamily)
    (f : Position → State) (hf : GloballyLegal f)
    (a : Position) (hgamma : (f a).1 = 0) :
    ∃ k : TileKind, ExactParentAt f a k ∧
      ∀ j : TileKind, ExactParentAt f a j → j = k :=
  exact_parent_of_universal_radiusFive_certificate certifiedParentFamily
    certifiedParentFamily_shape hcomplete f hf a hgamma

#check @certifiedFamily_every_cell_has_unique_owner
#check @certifiedFamily_every_Gamma_has_exact_framed_parent
#print axioms certifiedFamily_every_cell_has_unique_owner
#print axioms certifiedFamily_every_Gamma_has_exact_framed_parent
end SpectreFinite.HexSearch.ParentOwnership
