module

public import SparseMonotiles.AffineAvoidance
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Affine.Isometry

@[expose] public section

/-!
# Generic points of a fixed affine ridge

A finite (in fact countable) family of affine planes has a dense set of points
on a fixed nonempty affine ridge at which every active plane contains the
entire ridge. Thus the normals of all active supporting planes belong to the
same normal space. Its dimension is derived from the codimension-two equation;
neither a transverse sector partition nor an angle-sum premise is used.
-/

namespace SparseMonotiles

open Set AffineSubspace

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point of `R` is generic for `H` when every plane active there contains `R`.
This definition is relative to `R`, so density has its intrinsic topology. -/
def genericRidgePoints {ι : Type*} (R : AffineSubspace ℝ E)
    (H : ι → AffineSubspace ℝ E) : Set R :=
  {x | ∀ i, (x : E) ∈ H i → R ≤ H i}

/-- The inverse images of planes not containing the ridge are proper affine
subspaces in any affine coordinate chart of that ridge. -/
theorem ridge_comap_ne_top {V : Type*} [AddCommGroup V] [Module ℝ V]
    {R H : AffineSubspace ℝ E} [Nonempty R]
    (e : V ≃ᵃ[ℝ] R) (hRH : ¬ R ≤ H) :
    H.comap (R.subtype.comp e.toAffineMap) ≠ ⊤ := by
  intro htop
  apply hRH
  intro x hx
  have hm : e.symm ⟨x, hx⟩ ∈ H.comap (R.subtype.comp e.toAffineMap) := by
    rw [htop]
    exact mem_top _ _ _
  change (e (e.symm ⟨x, hx⟩) : E) ∈ H at hm
  simpa using hm

/-- Avoiding all planes not containing `R` is dense in `R`. No codimension
assumption on `R`, nor rank assumption on the family, is needed for this step. -/
theorem dense_genericRidgePoints [FiniteDimensional ℝ E]
    {ι : Type*} [Countable ι] (R : AffineSubspace ℝ E)
    (hR : (R : Set E).Nonempty) (H : ι → AffineSubspace ℝ E) :
    Dense (genericRidgePoints R H) := by
  classical
  letI : Nonempty R := hR.to_subtype
  let p : R := Classical.choice inferInstance
  let e : R.direction ≃ᵃⁱ[ℝ] R := AffineIsometryEquiv.vaddConst ℝ p
  let J := {i : ι // ¬ R ≤ H i}
  let L : J → AffineSubspace ℝ R.direction := fun i =>
    (H i.1).comap (R.subtype.comp e.toAffineMap)
  have hL : ∀ i, L i ≠ ⊤ := fun i => ridge_comap_ne_top e.toAffineEquiv i.property
  have hd := affineSubspaces_dense_avoid L hL
  apply (e.surjective.denseRange.dense_image e.continuous hd).mono
  rintro x ⟨v, hv, rfl⟩ i hi
  by_contra hRi
  exact hv ⟨i, hRi⟩ hi

/-- Every nonempty relatively open part of the ridge contains a generic point. -/
theorem exists_genericRidgePoint_in_open [FiniteDimensional ℝ E]
    {ι : Type*} [Countable ι] (R : AffineSubspace ℝ E)
    (hR : (R : Set E).Nonempty) (H : ι → AffineSubspace ℝ E)
    {O : Set R} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ x ∈ O, ∀ i, (x : E) ∈ H i → R ≤ H i :=
  (dense_genericRidgePoints R hR H).inter_open_nonempty O hO hne

/-- The codimension-two equation itself forces finite-dimensional ambient
space: an infinite-dimensional space has `finrank = 0`. -/
theorem finiteDimensional_of_ridge_codimension_two (R : AffineSubspace ℝ E)
    (hcodim : Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E) :
    FiniteDimensional ℝ E :=
  FiniteDimensional.of_finrank_pos (by omega)

/-- The density conclusion with only the exact ridge codimension equation. -/
theorem dense_genericRidgePoints_of_codimension_two
    {ι : Type*} [Countable ι] (R : AffineSubspace ℝ E)
    (hR : (R : Set E).Nonempty)
    (hcodim : Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E)
    (H : ι → AffineSubspace ℝ E) : Dense (genericRidgePoints R H) := by
  letI := finiteDimensional_of_ridge_codimension_two R hcodim
  exact dense_genericRidgePoints R hR H

/-- An affine equation, represented as an affine subspace, including possibly
empty or redundant equations. -/
def affineFormPlane (f : E →ᵃ[ℝ] ℝ) (c : ℝ) : AffineSubspace ℝ E :=
  (AffineSubspace.mk' c (⊥ : Submodule ℝ ℝ)).comap f

@[simp] theorem mem_affineFormPlane (f : E →ᵃ[ℝ] ℝ) (c : ℝ) (x : E) :
    x ∈ affineFormPlane f c ↔ f x = c := by
  simp [affineFormPlane, AffineSubspace.mem_mk', sub_eq_zero]

/-- An adapter for finite affine inequality inventories: generic active
equations vanish on the entire ridge. -/
theorem dense_ridge_affine_equations {ι : Type*} [Countable ι]
    (R : AffineSubspace ℝ E) (hR : (R : Set E).Nonempty)
    (hcodim : Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E)
    (f : ι → E →ᵃ[ℝ] ℝ) (c : ι → ℝ) :
    Dense {x : R | ∀ i, f i x = c i → ∀ y ∈ R, f i y = c i} := by
  apply (dense_genericRidgePoints_of_codimension_two R hR hcodim
    (fun i => affineFormPlane (f i) (c i))).mono
  intro x hx i hi y hy
  exact (mem_affineFormPlane _ _ _).mp
    (hx i ((mem_affineFormPlane _ _ _).mpr hi) hy)

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A normal to a plane containing a nonempty ridge is orthogonal to the
ridge direction. The plane's normal equation is the only geometric premise. -/
theorem normal_mem_ridge_orthogonal {R H : AffineSubspace ℝ E}
    (hR : (R : Set E).Nonempty) (hRH : R ≤ H) {N : E} {c : ℝ}
    (hplane : ∀ x ∈ H, inner (𝕜 := ℝ) N x = c) : N ∈ R.directionᗮ := by
  obtain ⟨p, hp⟩ := hR
  apply (Submodule.mem_orthogonal _ _).mpr
  intro v hv
  have hsum := hplane (v + p) (hRH (vadd_mem_of_mem_direction hv hp))
  have hbase := hplane p (hRH hp)
  rw [inner_add_right, hbase] at hsum
  rw [real_inner_comm]
  linarith

/-- The common normal space really is two-dimensional, derived by orthogonal
rank-nullity. Finite dimensionality is discharged from `hcodim`. -/
theorem ridge_orthogonal_finrank_two (R : AffineSubspace ℝ E)
    (hcodim : Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E) :
    Module.finrank ℝ R.directionᗮ = 2 := by
  letI := finiteDimensional_of_ridge_codimension_two R hcodim
  have hrank := R.direction.finrank_add_finrank_orthogonal
  omega

/-- At any generic point, all active neighboring-plane normals lie in the
same two-dimensional normal space. -/
theorem genericRidgePoint_active_normals {ι : Type*}
    (R : AffineSubspace ℝ E) (hR : (R : Set E).Nonempty)
    (hcodim : Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E)
    (H : ι → AffineSubspace ℝ E) (N : ι → E) (c : ι → ℝ)
    (hplane : ∀ i x, x ∈ H i → inner (𝕜 := ℝ) (N i) x = c i)
    {x : R} (hx : x ∈ genericRidgePoints R H) :
    Module.finrank ℝ R.directionᗮ = 2 ∧
      ∀ i, (x : E) ∈ H i → N i ∈ R.directionᗮ := by
  refine ⟨ridge_orthogonal_finrank_two R hcodim, ?_⟩
  intro i hi
  exact normal_mem_ridge_orthogonal hR (hx i hi) (hplane i)

/-- Direct dense generic-ridge bridge: every active neighboring plane contains
the ridge, and every corresponding normal lies in its two-dimensional normal
space. This applies to finite plane inventories through `[Countable ι]`. -/
theorem dense_genericRidgePoints_active_normals {ι : Type*} [Countable ι]
    (R : AffineSubspace ℝ E) (hR : (R : Set E).Nonempty)
    (hcodim : Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E)
    (H : ι → AffineSubspace ℝ E) (N : ι → E) (c : ι → ℝ)
    (hplane : ∀ i x, x ∈ H i → inner (𝕜 := ℝ) (N i) x = c i) :
    Module.finrank ℝ R.directionᗮ = 2 ∧
      Dense {x : R | ∀ i, (x : E) ∈ H i → R ≤ H i ∧ N i ∈ R.directionᗮ} := by
  refine ⟨ridge_orthogonal_finrank_two R hcodim, ?_⟩
  apply (dense_genericRidgePoints_of_codimension_two R hR hcodim H).mono
  intro x hx i hi
  exact ⟨hx i hi, normal_mem_ridge_orthogonal hR (hx i hi) (hplane i)⟩

/-- An independent subfamily of active normals at a generic ridge point has
at most two members. This excludes a neighboring triple independently of
any sector or angle-sum argument. -/
theorem genericRidgePoint_independent_active_card_le_two
    {ι κ : Type*} [Fintype κ]
    (R : AffineSubspace ℝ E) (hR : (R : Set E).Nonempty)
    (hcodim : Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E)
    (H : ι → AffineSubspace ℝ E) (N : ι → E) (c : ι → ℝ)
    (hplane : ∀ i x, x ∈ H i → inner (𝕜 := ℝ) (N i) x = c i)
    {x : R} (hx : x ∈ genericRidgePoints R H)
    (f : κ → ι) (hactive : ∀ j, (x : E) ∈ H (f j))
    (hN : LinearIndependent ℝ (N ∘ f)) : Fintype.card κ ≤ 2 := by
  letI := finiteDimensional_of_ridge_codimension_two R hcodim
  have hm (j : κ) : N (f j) ∈ R.directionᗮ :=
    normal_mem_ridge_orthogonal hR (hx (f j) (hactive j)) (hplane (f j))
  have hN' : LinearIndependent ℝ (fun j => (⟨N (f j), hm j⟩ : R.directionᗮ)) :=
    LinearIndependent.of_comp R.directionᗮ.subtype hN
  simpa only [ridge_orthogonal_finrank_two R hcodim] using hN'.fintype_card_le_finrank

end InnerProduct

#print axioms dense_genericRidgePoints
#print axioms finiteDimensional_of_ridge_codimension_two
#print axioms dense_ridge_affine_equations
#print axioms genericRidgePoint_independent_active_card_le_two
#print axioms normal_mem_ridge_orthogonal
#print axioms ridge_orthogonal_finrank_two
#print axioms dense_genericRidgePoints_active_normals

end SparseMonotiles
