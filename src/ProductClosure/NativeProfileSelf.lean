module

public import ProductClosure.NativeMonotileCriterion
public import ProductClosure.FacetCompatibility

@[expose] public section

/-! Identity has no opposed full-site match within a literal finite polycube.
The self-pair profile law follows from exposed-facet occupancy geometry. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration.NativeChair
noncomputable section
variable {m J : ℕ} {S : Finset (LatticeIndex m)}

/-- An identity site matching would give two self-opposed exposed carrier
facets at one center, contradicting literal missing-neighbor occupancy. -/
theorem not_siteTransport_identity (u v : Site S) :
    ¬ SiteTransport (IsometryEquiv.refl (Space m)) u v := by
  intro h
  have ht (j : Fin m) : siteAxis v j = siteAxis u j := by
    simpa only [placedNormal_refl] using h.1 j
  have hoff : siteOffset v = siteOffset u := by
    simp only [siteOffset]
    exact Finset.sum_congr rfl (fun j _ => congrArg (q0 j • ·) (ht j))
  have hc : facetCenter v.1 = facetCenter u.1 := by
    have hh : siteCenter v = siteCenter u := h.2.2
    simp only [siteCenter, hoff] at hh
    exact add_right_cancel hh
  have hn : outward v.1 = -outward u.1 := by
    simpa only [placedNormal_refl] using h.2.1
  exact Polycube.not_same_center_opposite_outward v.1 u.1 ⟨hc, hn⟩

/-- Identity profile matching is vacuous for every coefficient assignment. -/
theorem FullProfileMating_identity (a : Coefficients S J) :
    FullProfileMating a (IsometryEquiv.refl (Space m)) := by
  intro u v h
  exact (not_siteTransport_identity u v h).elim

theorem fullProfile_self_relative (a : Coefficients S J) (f : Space m ≃ᵢ Space m) :
    FullProfileMating a (relativePlacement f f) := by
  rw [relativePlacement_self]
  exact FullProfileMating_identity a

/-- A distinct-pair profile law extends to all world pairs because actual
self-geometry forbids identity matching. No coefficient argument is needed. -/
theorem CellWorldFullProfile_of_distinct (a : Coefficients S J)
    (W : World.CompleteTiling (World.placedCells S))
    (h : ∀ q r, q ∈ W.tiles → r ∈ W.tiles → q ≠ r →
      FullProfileMating a (poseIsometry (q.relative r))) : CellWorldFullProfile a W := by
  intro q r hq hr
  by_cases he : q = r
  · subst r
    rw [poseIsometry_relative]
    exact fullProfile_self_relative a (poseIsometry q)
  · exact h q r hq hr he

#print axioms not_siteTransport_identity
#print axioms FullProfileMating_identity
#print axioms CellWorldFullProfile_of_distinct
end
end ProductClosure.NativeCompiler
