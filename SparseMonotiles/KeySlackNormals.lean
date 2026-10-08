module

public import SparseMonotiles.CanonicalRidgeRank
public import Mathlib.Analysis.Normed.Affine.Isometry

@[expose] public section

/-! # Exact positively scaled supporting normals for actual key slacks -/
namespace SparseMonotiles

noncomputable def keyFacetScale {n : ℕ} (k : KeyData (n+1)) : PyramidFacetIndex n → ℝ
  | none => 1
  | some (i,b) => keySideDistance k i b

theorem keyFacetScale_pos {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b) (a : PyramidFacetIndex n) :
    0 < keyFacetScale k a := by
  cases a with
  | none => exact zero_lt_one
  | some u => exact hd u.1 u.2

theorem pyramidFacetSlopeNormal_ne_zero {n : ℕ} (s : Fin n → Bool → ℝ)
    (a : PyramidFacetIndex n) : pyramidFacetSlopeNormal s a ≠ 0 := by
  intro h
  have hx := congrArg (fun v : Point (n+1) => v (Fin.last n)) h
  cases a with
  | none => simp [pyramidFacetSlopeNormal, pyramidBaseNormal, EuclideanSpace.single_apply] at hx
  | some u => simp [pyramidFacetSlopeNormal] at hx

theorem key_facet_form_eq_scaled_inner {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b) (a : PyramidFacetIndex n) (x : Point (n+1)) :
    keyPyramidHalfspaceNormal k (pyramidFacetHalfspaceIndex a) x =
      keyFacetScale k a * inner (𝕜 := ℝ) (pyramidFacetSlopeNormal (keySideSlope k) a) x := by
  cases a with
  | none =>
      change -x (Fin.last n) = 1 * inner (𝕜 := ℝ) (pyramidBaseNormal n) x
      rw [inner_pyramidBaseNormal, one_mul]
  | some u => exact key_side_form_eq_distance_mul_inner k u.1 u.2 (hd u.1 u.2) x

theorem key_facet_slack_difference {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b) (a : PyramidFacetIndex n) (x p : Point (n+1)) :
    keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) x =
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) p +
        keyFacetScale k a * inner (𝕜 := ℝ) (-pyramidFacetSlopeNormal (keySideSlope k) a) (x-p) := by
  simp only [keyPyramidHalfspaceSlack, key_facet_form_eq_scaled_inner k hd a,
    inner_neg_left, inner_sub_right]
  ring

/-- Inward world normal under an arbitrary affine isometry, including reflections. -/
noncomputable def keyWorldInwardNormal {n : ℕ} (k : KeyData (n+1))
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (a : PyramidFacetIndex n) : Point (n+1) :=
  e.linearIsometryEquiv.symm (-pyramidFacetSlopeNormal (keySideSlope k) a)

theorem keyWorldInwardNormal_ne_zero {n : ℕ} (k : KeyData (n+1))
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (a : PyramidFacetIndex n) :
    keyWorldInwardNormal k e a ≠ 0 := by
  intro h
  have hn : -pyramidFacetSlopeNormal (keySideSlope k) a = 0 :=
    e.linearIsometryEquiv.symm.injective (h.trans (map_zero _).symm)
  exact pyramidFacetSlopeNormal_ne_zero (keySideSlope k) a (neg_eq_zero.mp hn)

/-- The exact affine world slack is a positive multiple of its inward-normal
linear form after subtracting its value at the chosen point. -/
theorem key_facet_world_slack_difference {n : ℕ} (k : KeyData (n+1))
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (a : PyramidFacetIndex n) (x p : Point (n+1)) :
    keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e x) =
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) (e p) +
        keyFacetScale k a * inner (𝕜 := ℝ) (keyWorldInwardNormal k e a) (x-p) := by
  rw [key_facet_slack_difference k hd a (e x) (e p)]
  congr 2
  have hmap : e x - e p = e.linearIsometryEquiv (x-p) := (e.map_vsub x p).symm
  rw [hmap]
  have hinner := e.linearIsometryEquiv.inner_map_map
    (keyWorldInwardNormal k e a) (x-p)
  simpa only [keyWorldInwardNormal, LinearIsometryEquiv.apply_symm_apply] using hinner

#print axioms key_facet_slack_difference
#print axioms keyWorldInwardNormal_ne_zero
#print axioms key_facet_world_slack_difference
end SparseMonotiles
