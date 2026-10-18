module

public import SpectreGeometry.PolygonProductKeyCreasePlaneGerms
public import PhysicalRegistration.IsometryTransport
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section


/-!
# Containing-plane normals of literal native creases

An affine plane containing an actual base crease, or an actual distinct-axis
side crease, has its normal in the span of that crease's two computed normals.
The proof uses an explicit generic witness and the exact open plane-intersection
germ. It assumes no affine-hull, rank, or germ condition in the native endpoints.
The conclusions also hold under every ambient isometric bijection, using its
Mazur–Ulam linear part for the placed normals.
-/

namespace SpectreGeometry.ProductCrease
open SpectreGeometry PhysicalRegistration
open scoped InnerProductSpace
open Set
noncomputable section

/-- A containing affine plane annihilates every direction tangent to an exact
open two-plane intersection germ. A positive step of size
`ε / (2 * (‖v‖ + 1))` stays in the germ; orthogonal complementation then gives
membership in the actual two-normal span. -/
theorem normal_mem_span_pair_of_local_plane_intersection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (C U : Set E) (x o p q n : E) (cp cq c : ℝ)
    (hU : IsOpen U) (hxU : x ∈ U) (hxC : x ∈ C)
    (hgerm : ∀ y ∈ U, y ∈ C ↔
      ⟪p, y - o⟫_ℝ = cp ∧ ⟪q, y - o⟫_ℝ = cq)
    (hcontain : ∀ y ∈ C, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ {p, q} := by
  let K : Submodule ℝ E := Submodule.span ℝ {p, q}
  have hdouble : n ∈ Kᗮᗮ := by
    apply (Kᗮ.mem_orthogonal' n).mpr
    intro v hv
    have hp : ⟪p, v⟫_ℝ = 0 :=
      (K.mem_orthogonal v).mp hv p (Submodule.subset_span (by simp))
    have hq : ⟪q, v⟫_ℝ = 0 :=
      (K.mem_orthogonal v).mp hv q (Submodule.subset_span (by simp))
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
    let r : ℝ := ε / (2 * (‖v‖ + 1))
    have hden : 0 < 2 * (‖v‖ + 1) := by positivity
    have hr : 0 < r := div_pos hε hden
    have hr_mul : r * (2 * (‖v‖ + 1)) = ε := by
      exact div_mul_cancel₀ ε hden.ne'
    have hstep : ‖r • v‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith [norm_nonneg v]
    have hyU : x + r • v ∈ U := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hstep
    have hxplanes := (hgerm x hxU).mp hxC
    have hyC : x + r • v ∈ C := by
      apply (hgerm (x + r • v) hyU).mpr
      rw [add_sub_right_comm, inner_add_right, inner_add_right,
        real_inner_smul_right, real_inner_smul_right, hp, hq]
      simpa using hxplanes
    have hy := hcontain (x + r • v) hyC
    rw [inner_add_right, real_inner_smul_right, hcontain x hxC] at hy
    have hz : r * ⟪n, v⟫_ℝ = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hr.ne'
  simpa only [K.orthogonal_orthogonal] using hdouble

/-- A two-normal containment statement transports through an unrestricted
ambient isometry. Only the constant changes when the translation is removed. -/
theorem normal_mem_span_pair_of_image_containment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (p q : E) (f : E ≃ᵢ E) (n : E) (c : ℝ)
    (hnative : ∀ n' c', (∀ y ∈ C, ⟪n', y⟫_ℝ = c') →
      n' ∈ Submodule.span ℝ {p, q})
    (hcontain : ∀ y ∈ f '' C, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ
      {f.toRealAffineIsometryEquiv.linearIsometryEquiv p,
       f.toRealAffineIsometryEquiv.linearIsometryEquiv q} := by
  let L := f.toRealAffineIsometryEquiv.linearIsometryEquiv
  have hpull : ∀ y ∈ C, ⟪L.symm n, y⟫_ℝ = c - ⟪n, f 0⟫_ℝ := by
    intro y hy
    have hfy : f y = f 0 + L y := by
      simpa only [zero_add, IsometryEquiv.coeFn_toRealAffineIsometryEquiv] using
        affineIsometry_map_add f.toRealAffineIsometryEquiv (0 : E) y
    have hinner : ⟪n, L y⟫_ℝ = ⟪L.symm n, y⟫_ℝ := by
      simpa only [L.apply_symm_apply] using L.inner_map_map (L.symm n) y
    have h := hcontain (f y) ⟨y, hy, rfl⟩
    rw [hfy, inner_add_right, hinner] at h
    linarith
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp (hnative _ _ hpull)
  apply Submodule.mem_span_pair.mpr
  refine ⟨r, s, ?_⟩
  have h := congrArg L hrs
  simpa only [map_add, map_smul, L.apply_symm_apply] using h


/-- Every affine plane containing the actual native base crease has its normal
in the span of the actual outward and side normals. -/
theorem baseCrease_containing_normal_mem_span (u : ProductKeySite) (s : ProductKeySide) (n : EFour) (c : ℝ)
    (hcontain : ∀ y ∈ baseCrease u s, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ {productKeyOutwardNormal u, productKeySideNormal u s} := by
  obtain ⟨x, hx⟩ := baseGeneric_nonempty u s
  obtain ⟨U, hU, hxU, hgerm⟩ :=
    baseGeneric_locally_eq_plane_intersection u s x hx
  exact normal_mem_span_pair_of_local_plane_intersection
    (baseCrease u s) U x (productKeyCenter u) (productKeyOutwardNormal u) (productKeySideNormal u s) n
    0 (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) c hU hxU hx.1 hgerm hcontain

/-- Every affine plane containing the actual native distinct-axis side crease
has its normal in the span of the two actual side normals. -/
theorem sideCrease_containing_normal_mem_span (u : ProductKeySite) (s t : ProductKeySide) (hst : s.1 ≠ t.1)
    (n : EFour) (c : ℝ)
    (hcontain : ∀ y ∈ sideCrease u s t, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ {productKeySideNormal u s, productKeySideNormal u t} := by
  obtain ⟨x, hx⟩ := sideGeneric_nonempty u s t hst
  obtain ⟨U, hU, hxU, hgerm⟩ :=
    sideGeneric_locally_eq_plane_intersection u s t x hx
  exact normal_mem_span_pair_of_local_plane_intersection
    (sideCrease u s t) U x (productKeyCenter u) (productKeySideNormal u s) (productKeySideNormal u t) n
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN)
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) c hU hxU hx.1 hgerm hcontain

/-- The base-crease normal-span conclusion for an arbitrary ambient placement. -/
theorem placed_baseCrease_containing_normal_mem_span (u : ProductKeySite) (s : ProductKeySide)
    (f : EFour ≃ᵢ EFour) (n : EFour) (c : ℝ)
    (hcontain : ∀ y ∈ f '' baseCrease u s, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ
      {f.toRealAffineIsometryEquiv.linearIsometryEquiv (productKeyOutwardNormal u), f.toRealAffineIsometryEquiv.linearIsometryEquiv (productKeySideNormal u s)} := by
  exact normal_mem_span_pair_of_image_containment (baseCrease u s)
    (productKeyOutwardNormal u) (productKeySideNormal u s) f n c
    (fun n' c' h => baseCrease_containing_normal_mem_span u s n' c' h) hcontain

/-- The distinct-axis side-crease normal-span conclusion for an arbitrary
ambient placement, with no restriction on its orthogonal linear part. -/
theorem placed_sideCrease_containing_normal_mem_span (u : ProductKeySite) (s t : ProductKeySide) (hst : s.1 ≠ t.1)
    (f : EFour ≃ᵢ EFour) (n : EFour) (c : ℝ)
    (hcontain : ∀ y ∈ f '' sideCrease u s t, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ
      {f.toRealAffineIsometryEquiv.linearIsometryEquiv (productKeySideNormal u s), f.toRealAffineIsometryEquiv.linearIsometryEquiv (productKeySideNormal u t)} := by
  exact normal_mem_span_pair_of_image_containment (sideCrease u s t)
    (productKeySideNormal u s) (productKeySideNormal u t) f n c
    (fun n' c' h => sideCrease_containing_normal_mem_span u s t hst n' c' h) hcontain


end
end SpectreGeometry.ProductCrease
