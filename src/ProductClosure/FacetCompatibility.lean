module

public import ProductClosure.CarrierLocal

@[expose] public section

/-! No self-opposed exposed facet in a literal finite occupied carrier. -/
namespace ProductClosure.Polycube
noncomputable section
variable {d : ℕ} {S : Finset (LatticeIndex d)}

theorem axis_eq_of_opposite_outward {f g : Facet S} (hn : outward f = -outward g) :
    f.axis = g.axis := by
  by_contra hne
  have hv := congrArg (fun v : Space d => v f.axis) hn
  simp only [PiLp.neg_apply, outward_apply, ↓reduceIte, if_neg hne, neg_zero] at hv
  have hh := abs_sign f.positive
  rw [hv] at hh
  norm_num at hh

/-- Literal missing-neighbor geometry excludes opposed facets at the same
center within one carrier. This is the cross-product-type exclusion input. -/
theorem not_same_center_opposite_outward (f g : Facet S) :
    ¬(facetCenter f = facetCenter g ∧ outward f = -outward g) := by
  rintro ⟨hc, hn⟩
  have ha := axis_eq_of_opposite_outward hn
  have hp : facetPlane f = facetPlane g := by
    have hh := congrArg (fun v : Space d => v f.axis) hc
    rw [facetCenter_normal, ha, facetCenter_normal] at hh
    exact Int.cast_injective hh
  have ht : ∀ k, k ≠ f.axis → f.cell.val k = g.cell.val k := by
    intro k hk
    have hh := congrArg (fun v : Space d => v k) hc
    rw [facetCenter_tangent f k hk, facetCenter_tangent g k (ha ▸ hk)] at hh
    exact Int.cast_injective (add_right_cancel hh)
  have he := facet_eq_of_coordinates f g ha hp ht
  subst g
  have hv := congrArg (fun v : Space d => v f.axis) hn
  simp only [PiLp.neg_apply, outward_apply, ↓reduceIte] at hv
  cases hp : f.positive <;> norm_num [sign, hp] at hv

end
end ProductClosure.Polycube
