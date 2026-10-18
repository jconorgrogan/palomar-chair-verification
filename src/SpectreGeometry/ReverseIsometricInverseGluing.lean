module

public import SpectreGeometry.ReverseInverseDeformationGlue

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Deformation
open scoped NNReal

/-- The exact inverse residual bound is invariant under a simultaneous
Euclidean rotation and arbitrary distinct source/target translations. -/
theorem inverse_residual_lipschitz_placed
    (G : EPlane → EPlane)
    (hG : LipschitzWith (15/16 : ℝ≥0) (fun x => x-(31/32:ℝ) • G x))
    (R : EPlane ≃ₗᵢ[ℝ] EPlane) (a b : EPlane) :
    LipschitzWith (15/16 : ℝ≥0)
      (fun x => x-(31/32:ℝ) • (a+R (G (R.symm (x-b))))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let u := R.symm (x-b)
  let v := R.symm (y-b)
  have he : (x-(31/32:ℝ) • (a+R (G u))) -
      (y-(31/32:ℝ) • (a+R (G v))) =
      R ((u-(31/32:ℝ) • G u)-(v-(31/32:ℝ) • G v)) := by
    simp only [map_sub,map_smul,u,v,LinearIsometryEquiv.apply_symm_apply,smul_add]
    abel
  rw [dist_eq_norm,he,R.norm_map,←dist_eq_norm]
  have h := hG.dist_le_mul u v
  have huv : dist u v = dist x y := by
    rw [show dist u v = dist (R u) (R v) from (R.dist_map u v).symm]
    simp only [u,v,LinearIsometryEquiv.apply_symm_apply,dist_sub_right]
  rwa [huv] at h

variable {ι : Type*}

def residualCoverMap (C : ι → Set EPlane) (hcover : ∀ x, ∃ j, x ∈ C j)
    (G : ι → EPlane → EPlane) (x : EPlane) : EPlane :=
  G (Classical.choose (hcover x)) x

theorem residualCoverMap_on (C : ι → Set EPlane) (hcover : ∀ x, ∃ j, x ∈ C j)
    (G : ι → EPlane → EPlane)
    (hagree : ∀ i j x, x ∈ C i → x ∈ C j → G i x=G j x)
    (j : ι) (x : EPlane) (hx : x ∈ C j) : residualCoverMap C hcover G x = G j x :=
  hagree _ j x (Classical.choose_spec (hcover x)) hx

theorem residualCoverMap_lipschitz (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j) (G : ι → EPlane → EPlane)
    (hagree : ∀ i j x, x ∈ C i → x ∈ C j → G i x=G j x)
    (hres : ∀ j, LipschitzWith (15/16 : ℝ≥0) (fun x => x-(31/32:ℝ) • G j x)) :
    LipschitzWith (15/16 : ℝ≥0)
      (fun x => x-(31/32:ℝ) • residualCoverMap C hcover G x) := by
  apply lipschitz_of_locallyFinite_closed_cover C hlocal hclosed hcover
  intro j
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [residualCoverMap_on C hcover G hagree j x hx,
    residualCoverMap_on C hcover G hagree j y hy]
  exact (hres j).dist_le_mul x y

/-- Compatible placed inverse charts yield a genuine whole-plane
homeomorphism. Global injectivity, surjectivity and target coverage are derived
from the residual estimate rather than assumed. -/
def placedInverseCoverHomeomorph (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j) (G : ι → EPlane → EPlane)
    (hagree : ∀ i j x, x ∈ C i → x ∈ C j → G i x=G j x)
    (hres : ∀ j, LipschitzWith (15/16 : ℝ≥0) (fun x => x-(31/32:ℝ) • G j x)) :
    EPlane ≃ₜ EPlane :=
  inverseDeformationHomeomorph (residualCoverMap C hcover G)
    (residualCoverMap_lipschitz C hlocal hclosed hcover G hagree hres)

theorem placedInverseCoverHomeomorph_on (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j) (G : ι → EPlane → EPlane)
    (hagree : ∀ i j x, x ∈ C i → x ∈ C j → G i x=G j x)
    (hres : ∀ j, LipschitzWith (15/16 : ℝ≥0) (fun x => x-(31/32:ℝ) • G j x))
    (j : ι) (x : EPlane) (hx : x ∈ C j) :
    placedInverseCoverHomeomorph C hlocal hclosed hcover G hagree hres x = G j x := by
  rw [placedInverseCoverHomeomorph,inverseDeformationHomeomorph_apply]
  exact residualCoverMap_on C hcover G hagree j x hx

end
end SpectreGeometry.ReverseExistence
