module

public import SpectreGeometry.ReverseInverseDeformation
public import Mathlib.Analysis.Convex.Hull

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Deformation

def forwardChartAffine (k i : Fin 12) (a b : EPlane) : EPlane →ᵃ[ℝ] EPlane where
  toFun := affineEuclidean k i a b
  linear := matrixEuclideanLinear k i
  map_vadd' p v := by
    simp only [affineEuclidean,vadd_eq_add,map_add,map_sub]
    abel

def forwardChartEquiv (k i : Fin 12) (a b : EPlane) : EPlane ≃ᵃ[ℝ] EPlane :=
  AffineEquiv.ofBijective (φ := forwardChartAffine k i a b) ⟨
    (fun x y h => (forwardAffineChart k i a b).injective (by
      change affineEuclidean k i a b x = affineEuclidean k i a b y at h
      simpa only [forwardAffineChart_apply] using h)),
    (fun y => ⟨inverseAffineChart k i a b y,affine_inverse_chart k i a b y⟩)⟩

@[simp] theorem forwardChartEquiv_apply (k i : Fin 12) (a b x : EPlane) :
    forwardChartEquiv k i a b x = affineEuclidean k i a b x := rfl

def inverseChartAffine (k i : Fin 12) (a b : EPlane) : EPlane →ᵃ[ℝ] EPlane :=
  (forwardChartEquiv k i a b).symm.toAffineMap

@[simp] theorem inverseChartAffine_apply (k i : Fin 12) (a b x : EPlane) :
    inverseChartAffine k i a b x = inverseAffineChart k i a b x := by
  apply (forwardAffineChart k i a b).injective
  simp only [forwardAffineChart_apply,affine_inverse_chart]
  exact (forwardChartEquiv k i a b).apply_symm_apply x

/-- Inverse charts agreeing on shared vertices agree on their full shared
convex face. The common-face carrier binding is supplied separately. -/
theorem inverseAffineChart_agree_on_hull (k i l j : Fin 12) (a b c d : EPlane)
    (s : Set EPlane)
    (hv : Set.EqOn (inverseAffineChart k i a b) (inverseAffineChart l j c d) s) :
    Set.EqOn (inverseAffineChart k i a b) (inverseAffineChart l j c d) (convexHull ℝ s) := by
  have he : Set.EqOn (inverseChartAffine k i a b) (inverseChartAffine l j c d) s := by
    intro x hx
    simpa only [inverseChartAffine_apply] using hv hx
  intro x hx
  have h := AffineMap.eqOn_affineSpan he (convexHull_subset_affineSpan _ hx)
  simpa only [inverseChartAffine_apply] using h

theorem inverseAffineChart_lineMap (k i : Fin 12) (a b x y : EPlane) (t : ℝ) :
    inverseAffineChart k i a b (AffineMap.lineMap x y t) =
      AffineMap.lineMap (inverseAffineChart k i a b x) (inverseAffineChart k i a b y) t := by
  simpa only [inverseChartAffine_apply] using (inverseChartAffine k i a b).apply_lineMap x y t

end
end SpectreGeometry.ReverseExistence
