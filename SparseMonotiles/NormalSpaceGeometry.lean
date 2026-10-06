module

public import SparseMonotiles.OrthogonalTransverseSection
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.Normed.Affine.MazurUlam

@[expose] public section

/-!
# Supporting forms in the genuine ridge normal space

These adapters retain actual, possibly nonunit inward normals. Positive scale
factors are removed only from inequalities. Both the Euclidean normal angles
and arbitrary affine-isometry transport are exact.
-/
namespace SparseMonotiles
namespace NormalSpaceGeometry

open Set InnerProductGeometry

section Restriction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restrict an actual ambient normal, without normalization or projection. -/
def restrictedNormal (V : Submodule ℝ E) (n : E) (hn : n ∈ V) : V := ⟨n, hn⟩

@[simp] theorem coe_restrictedNormal (V : Submodule ℝ E) (n : E) (hn : n ∈ V) :
    (restrictedNormal V n hn : E) = n := rfl

@[simp] theorem norm_restrictedNormal (V : Submodule ℝ E) (n : E) (hn : n ∈ V) :
    ‖restrictedNormal V n hn‖ = ‖n‖ := rfl

@[simp] theorem restrictedNormal_ne_zero (V : Submodule ℝ E) (n : E) (hn : n ∈ V) :
    restrictedNormal V n hn ≠ 0 ↔ n ≠ 0 := by
  simp [restrictedNormal, Subtype.ext_iff]

@[simp] theorem inner_restrictedNormal (V : Submodule ℝ E) (n m : E)
    (hn : n ∈ V) (hm : m ∈ V) :
    inner (𝕜 := ℝ) (restrictedNormal V n hn) (restrictedNormal V m hm) =
      inner (𝕜 := ℝ) n m := rfl

/-- Intrinsic angles equal the actual ambient angles, even without unit normals. -/
theorem angle_restrictedNormal (V : Submodule ℝ E) (n m : E)
    (hn : n ∈ V) (hm : m ∈ V) :
    angle (restrictedNormal V n hn) (restrictedNormal V m hm) = angle n m :=
  (V.angle_coe (restrictedNormal V n hn) (restrictedNormal V m hm)).symm

/-- A nonzero scaled supporting normal belongs to the common normal space as
soon as its actual supporting equation vanishes on the ridge. -/
theorem supporting_normal_mem_ridge_orthogonal
    (R : AffineSubspace ℝ E) {p : E} (hp : p ∈ R)
    (f : E → ℝ) (n : E) {c : ℝ} (hc : c ≠ 0)
    (hform : ∀ x, f x = f p + c * inner (𝕜 := ℝ) n (x - p))
    (hzero : ∀ x ∈ R, f x = 0) : n ∈ R.directionᗮ := by
  apply normal_mem_ridge_orthogonal ⟨p, hp⟩ (le_refl R)
    (N := n) (c := inner (𝕜 := ℝ) n p)
  intro x hx
  have h := hform x
  rw [hzero x hx, hzero p hp, zero_add] at h
  have hz : inner (𝕜 := ℝ) n (x - p) = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left hc
  rw [inner_sub_right] at hz
  exact sub_eq_zero.mp hz

/-- An affine linear-part normal gives the requested base-point representation. -/
theorem affine_form_eq_at_base (f : E →ᵃ[ℝ] ℝ) (n : E) (c : ℝ)
    (hlinear : ∀ v, f.linear v = c * inner (𝕜 := ℝ) n v) (p x : E) :
    f x = f p + c * inner (𝕜 := ℝ) n (x - p) := by
  have h := f.linearMap_vsub x p
  change f.linear (x - p) = f x - f p at h
  rw [hlinear] at h
  linarith

end Restriction

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The orthogonal projection preserves the inner product against a true normal. -/
theorem inner_restrictedNormal_projection (R : AffineSubspace ℝ E) (p n x : E)
    (hn : n ∈ R.directionᗮ) :
    inner (𝕜 := ℝ) (restrictedNormal R.directionᗮ n hn) (ridgeNormalProjection R p x) =
      inner (𝕜 := ℝ) n (x - p) :=
  R.directionᗮ.inner_orthogonalProjection_eq_of_mem_left
    (restrictedNormal R.directionᗮ n hn) (x - p)

/-- Exact factorization of the entire active supporting slack. -/
theorem supporting_slack_eq_normal_projection
    (R : AffineSubspace ℝ E) (p : E) (f : E → ℝ) (n : E) (c : ℝ)
    (hn : n ∈ R.directionᗮ) (hp : f p = 0)
    (hform : ∀ x, f x = f p + c * inner (𝕜 := ℝ) n (x - p)) (x : E) :
    f x = c * inner (𝕜 := ℝ) (restrictedNormal R.directionᗮ n hn)
      (ridgeNormalProjection R p x) := by
  rw [inner_restrictedNormal_projection, hform, hp, zero_add]

/-- Both closed orientations of a supporting halfspace pull back exactly. -/
theorem supporting_halfspace_pullbacks
    (R : AffineSubspace ℝ E) (p : E) (f : E → ℝ) (n : E) {c : ℝ}
    (hc : 0 < c) (hn : n ∈ R.directionᗮ) (hp : f p = 0)
    (hform : ∀ x, f x = f p + c * inner (𝕜 := ℝ) n (x - p)) :
    {x | 0 ≤ f x} = ridgeNormalProjection R p ⁻¹'
      {v | 0 ≤ inner (𝕜 := ℝ) (restrictedNormal R.directionᗮ n hn) v} ∧
    {x | f x ≤ 0} = ridgeNormalProjection R p ⁻¹'
      {v | 0 ≤ inner (𝕜 := ℝ) (-restrictedNormal R.directionᗮ n hn) v} := by
  constructor
  · ext x
    change 0 ≤ f x ↔ 0 ≤ inner (𝕜 := ℝ) (restrictedNormal R.directionᗮ n hn)
      (ridgeNormalProjection R p x)
    rw [supporting_slack_eq_normal_projection R p f n c hn hp hform]
    exact mul_nonneg_iff_of_pos_left hc
  · ext x
    change f x ≤ 0 ↔ 0 ≤ inner (𝕜 := ℝ) (-restrictedNormal R.directionᗮ n hn)
      (ridgeNormalProjection R p x)
    rw [supporting_slack_eq_normal_projection R p f n c hn hp hform,
      inner_neg_left, neg_nonneg]
    constructor
    · intro h; nlinarith
    · exact mul_nonpos_of_nonneg_of_nonpos hc.le

/-- A single ready-to-use adapter for actual key or carrier supporting forms.
The returned normal is the same ambient vector, so angle transport is exact. -/
theorem active_supporting_slack_adapter
    (R : AffineSubspace ℝ E) {p : E} (hp : p ∈ R)
    (f : E → ℝ) (n : E) (hne : n ≠ 0) {c : ℝ} (hc : 0 < c)
    (hform : ∀ x, f x = f p + c * inner (𝕜 := ℝ) n (x - p))
    (hzero : ∀ x ∈ R, f x = 0) :
    ∃ nR : R.directionᗮ,
      (nR : E) = n ∧ nR ≠ 0 ∧ ‖nR‖ = ‖n‖ ∧
      (∀ x, f x = c * inner (𝕜 := ℝ) nR (ridgeNormalProjection R p x)) ∧
      {x | 0 ≤ f x} = ridgeNormalProjection R p ⁻¹' {v | 0 ≤ inner (𝕜 := ℝ) nR v} ∧
      {x | f x ≤ 0} = ridgeNormalProjection R p ⁻¹' {v | 0 ≤ inner (𝕜 := ℝ) (-nR) v} := by
  have hn := supporting_normal_mem_ridge_orthogonal R hp f n hc.ne' hform hzero
  refine ⟨restrictedNormal R.directionᗮ n hn, rfl, ?_, rfl, ?_, ?_⟩
  · exact (restrictedNormal_ne_zero _ _ _).mpr hne
  · exact supporting_slack_eq_normal_projection R p f n c hn (hzero p hp) hform
  · exact supporting_halfspace_pullbacks R p f n hc hn (hzero p hp) hform

/-- The supporting form on the true normal section is homogeneous with its
original positive scale, rather than only sign-equivalent. -/
theorem supporting_slack_on_normal_section
    (R : AffineSubspace ℝ E) (p : E) (f : E → ℝ) (n : E) (c : ℝ)
    (hn : n ∈ R.directionᗮ) (hp : f p = 0)
    (hform : ∀ x, f x = f p + c * inner (𝕜 := ℝ) n (x - p))
    (v : R.directionᗮ) :
    f (p + (v : E)) = c * inner (𝕜 := ℝ) (restrictedNormal R.directionᗮ n hn) v := by
  simpa only [ridgeNormalProjection_section] using
    supporting_slack_eq_normal_projection R p f n c hn hp hform (p + (v : E))

end Projection

section IsometricTransport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The inward normal in world coordinates for a world-to-canonical frame. -/
noncomputable def transportedNormal (a : F ≃ᵃⁱ[ℝ] E) (n : E) : F := a.linearIsometryEquiv.symm n

@[simp] theorem norm_transportedNormal (a : F ≃ᵃⁱ[ℝ] E) (n : E) :
    ‖transportedNormal a n‖ = ‖n‖ := a.linearIsometryEquiv.symm.norm_map n

@[simp] theorem transportedNormal_ne_zero (a : F ≃ᵃⁱ[ℝ] E) (n : E) :
    transportedNormal a n ≠ 0 ↔ n ≠ 0 := by
  simp [transportedNormal]

/-- The arbitrary physical frame preserves ordinary Euclidean normal angles. -/
theorem angle_transportedNormal (a : F ≃ᵃⁱ[ℝ] E) (n m : E) :
    angle (transportedNormal a n) (transportedNormal a m) = angle n m :=
  a.linearIsometryEquiv.symm.toLinearIsometry.angle_map n m

/-- Transport through an arbitrary affine isometry gives the exact world
supporting-form equation at the world base point. -/
theorem supporting_form_isometric_transport (a : F ≃ᵃⁱ[ℝ] E)
    (f : E → ℝ) (n : E) (c : ℝ) (p : F)
    (hform : ∀ y, f y = f (a p) + c * inner (𝕜 := ℝ) n (y - a p)) (x : F) :
    f (a x) = f (a p) + c * inner (𝕜 := ℝ) (transportedNormal a n) (x - p) := by
  rw [hform (a x)]
  have hmap := a.map_vsub x p
  change a.linearIsometryEquiv (x - p) = a x - a p at hmap
  rw [← hmap]
  congr 2
  rw [← a.linearIsometryEquiv.inner_map_map,
    show a.linearIsometryEquiv (transportedNormal a n) = n from
      a.linearIsometryEquiv.apply_symm_apply n]

/-- Isometric transport followed by restriction to the normal subspace still
preserves the original canonical angle exactly. -/
theorem angle_restricted_transportedNormal (a : F ≃ᵃⁱ[ℝ] E)
    (V : Submodule ℝ F) (n m : E)
    (hn : transportedNormal a n ∈ V) (hm : transportedNormal a m ∈ V) :
    angle (restrictedNormal V (transportedNormal a n) hn)
      (restrictedNormal V (transportedNormal a m) hm) = angle n m := by
  rw [angle_restrictedNormal, angle_transportedNormal]


/-- The common bound-minus-positive-scale-outward-normal convention becomes
exactly the inward-normal form used by the normal-space adapter. -/
theorem outward_supporting_form_isometric_transport (a : F ≃ᵃⁱ[ℝ] E)
    (f : E → ℝ) (n : E) (c : ℝ) (p : F)
    (hform : ∀ y, f y = f (a p) - c * inner (𝕜 := ℝ) n (y - a p)) (x : F) :
    f (a x) = f (a p) + c * inner (𝕜 := ℝ) (transportedNormal a (-n)) (x - p) := by
  apply supporting_form_isometric_transport a f (-n) c p _ x
  intro y
  rw [hform y, inner_neg_left]
  ring

/-- The complete adapter can be used directly in a physical frame, while its
returned ambient normal remains visibly the inverse-isometric canonical one. -/
theorem active_isometric_supporting_slack_adapter [FiniteDimensional ℝ F]
    (a : F ≃ᵃⁱ[ℝ] E) (R : AffineSubspace ℝ F) {p : F} (hp : p ∈ R)
    (f : E → ℝ) (n : E) (hne : n ≠ 0) {c : ℝ} (hc : 0 < c)
    (hform : ∀ y, f y = f (a p) + c * inner (𝕜 := ℝ) n (y - a p))
    (hzero : ∀ x ∈ R, f (a x) = 0) :
    ∃ nR : R.directionᗮ,
      (nR : F) = transportedNormal a n ∧ nR ≠ 0 ∧ ‖nR‖ = ‖transportedNormal a n‖ ∧
      (∀ x, f (a x) = c * inner (𝕜 := ℝ) nR (ridgeNormalProjection R p x)) ∧
      {x | 0 ≤ f (a x)} = ridgeNormalProjection R p ⁻¹' {v | 0 ≤ inner (𝕜 := ℝ) nR v} ∧
      {x | f (a x) ≤ 0} = ridgeNormalProjection R p ⁻¹' {v | 0 ≤ inner (𝕜 := ℝ) (-nR) v} := by
  exact active_supporting_slack_adapter R hp (fun x => f (a x)) (transportedNormal a n)
    ((transportedNormal_ne_zero a n).mpr hne) hc
    (supporting_form_isometric_transport a f n c p hform) hzero

end IsometricTransport

#print axioms supporting_normal_mem_ridge_orthogonal
#print axioms active_supporting_slack_adapter
#print axioms supporting_halfspace_pullbacks
#print axioms angle_restricted_transportedNormal
#print axioms supporting_form_isometric_transport
#print axioms outward_supporting_form_isometric_transport
#print axioms active_isometric_supporting_slack_adapter

end NormalSpaceGeometry
end SparseMonotiles
