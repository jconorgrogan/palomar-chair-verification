module

public import SpectreGeometry.DeformationHomeomorphism
public import SpectreGeometry.DeformationHomeomorphismAffine
public import SpectreGeometry.DeformationHomeomorphismGluing

@[expose] public section


/-! Assembly of the quantitative local certificates. The physical application
must supply the genuinely derived closed triangle cover and its affine formulas. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set
open scoped NNReal

theorem locallyFinite_finite_refinement {X ι κ : Type*} [TopologicalSpace X] [Finite κ]
    (S : ι → Set X) (C : ι × κ → Set X) (hS : LocallyFinite S)
    (hsub : ∀ i j, C (i,j) ⊆ S i) : LocallyFinite C := by
  intro x
  obtain ⟨U,hU,hfin⟩ := hS x
  refine ⟨U,hU,(hfin.prod (Set.finite_univ : (univ : Set κ).Finite)).subset ?_⟩
  rintro ⟨i,j⟩ ⟨y,hy,hyU⟩
  exact ⟨⟨y,hsub i j hy,hyU⟩,mem_univ j⟩

theorem residual_lipschitz_of_affine_cover {ι : Type*}
    (C : ι → Set EPlane) (hlocal : LocallyFinite C) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ x, ∃ i, x ∈ C i)
    (k j : ι → Fin 12) (a b : ι → EPlane) (F : EPlane → EPlane)
    (hF : ∀ i x, x ∈ C i → F x = affineEuclidean (k i) (j i) (a i) (b i) x) :
    LipschitzWith (15/16 : ℝ≥0) (fun x => x - (1/8 : ℝ) • F x) := by
  apply lipschitz_of_locallyFinite_closed_cover C hlocal hclosed hcover
  intro i
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [hF i x hx,hF i y hy]
  exact (affineEuclidean_residual_lipschitz (k i) (j i) (a i) (b i)).dist_le_mul x y

/-- The triangle cover and exact affine formulas imply global inversion.
There is no supplied injectivity, surjectivity, or properness premise. -/
def homeomorphOfAffineCover {ι : Type*}
    (C : ι → Set EPlane) (hlocal : LocallyFinite C) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ x, ∃ i, x ∈ C i)
    (k j : ι → Fin 12) (a b : ι → EPlane) (F : EPlane → EPlane)
    (hF : ∀ i x, x ∈ C i → F x = affineEuclidean (k i) (j i) (a i) (b i) x) :
    EPlane ≃ₜ EPlane :=
  ofEighthResidual F (15/16) (by norm_num)
    (residual_lipschitz_of_affine_cover C hlocal hclosed hcover k j a b F hF)

@[simp] theorem homeomorphOfAffineCover_apply {ι : Type*}
    (C : ι → Set EPlane) (hlocal : LocallyFinite C) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ x, ∃ i, x ∈ C i)
    (k j : ι → Fin 12) (a b : ι → EPlane) (F : EPlane → EPlane)
    (hF : ∀ i x, x ∈ C i → F x = affineEuclidean (k i) (j i) (a i) (b i) x)
    (x : EPlane) : homeomorphOfAffineCover C hlocal hclosed hcover k j a b F hF x = F x :=
  ofEighthResidual_apply _ _ _ _ _

end
end SpectreGeometry.Deformation
