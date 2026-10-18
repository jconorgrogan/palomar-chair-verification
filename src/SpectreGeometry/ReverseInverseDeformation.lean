module

public import SpectreGeometry.ReverseInverseContraction
public import SpectreGeometry.DeformationHomeomorphismAffine
public import SpectreGeometry.DeformationHomeomorphismGluing
public import SpectreGeometry.DeformationHomeomorphism

@[expose] public section


/-! Actual inverses of the checked forward affine charts, and a constructive
global inverse-deformation theorem. All norm estimates are in EPlane, the
Euclidean Hilbert plane, not the default sup norm on a pair of reals. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Deformation
open scoped NNReal

def forwardAffineChart (k i : Fin 12) (a b : EPlane) : EPlane ≃ₜ EPlane :=
  ofEighthResidual (affineEuclidean k i a b) (15/16) (by norm_num)
    (affineEuclidean_residual_lipschitz k i a b)

@[simp] theorem forwardAffineChart_apply (k i : Fin 12) (a b x : EPlane) :
    forwardAffineChart k i a b x = affineEuclidean k i a b x :=
  ofEighthResidual_apply _ _ _ _ x

def inverseAffineChart (k i : Fin 12) (a b : EPlane) : EPlane ≃ₜ EPlane :=
  (forwardAffineChart k i a b).symm

@[simp] theorem affine_inverse_chart (k i : Fin 12) (a b x : EPlane) :
    affineEuclidean k i a b (inverseAffineChart k i a b x) = x := by
  rw [←forwardAffineChart_apply]
  exact (forwardAffineChart k i a b).apply_symm_apply x

@[simp] theorem inverse_affine_chart (k i : Fin 12) (a b x : EPlane) :
    inverseAffineChart k i a b (affineEuclidean k i a b x) = x := by
  rw [←forwardAffineChart_apply]
  exact (forwardAffineChart k i a b).symm_apply_apply x

theorem inverseAffineChart_residual_lipschitz (k i : Fin 12) (a b : EPlane) :
    LipschitzWith (15/16 : ℝ≥0)
      (fun x => x-(31/32 : ℝ) • inverseAffineChart k i a b x) :=
  inverse_residual_lipschitz _ _ (affine_inverse_chart k i a b)
    (affineEuclidean_residual_lipschitz k i a b)

/-- A compatible map that inverts the certified affine chart on each member
of an actual locally finite closed plane cover has a global residual bound. -/
theorem inverseCover_residual_lipschitz {ι : Type*} (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j)
    (k i : ι → Fin 12) (a b : ι → EPlane) (G : EPlane → EPlane)
    (hchart : ∀ j x, x ∈ C j → affineEuclidean (k j) (i j) (a j) (b j) (G x) = x) :
    LipschitzWith (15/16 : ℝ≥0) (fun x => x-(31/32 : ℝ) • G x) := by
  apply lipschitz_of_locallyFinite_closed_cover C hlocal hclosed hcover
  intro j
  exact inverse_residual_lipschitzOn _ G (C j) (hchart j)
    (affineEuclidean_residual_lipschitz (k j) (i j) (a j) (b j))

/-- Banach inversion with the exact inverse-deformation scaling. -/
def inverseDeformationHomeomorph (G : EPlane → EPlane)
    (hG : LipschitzWith (15/16 : ℝ≥0) (fun x => x-(31/32 : ℝ) • G x)) :
    EPlane ≃ₜ EPlane :=
  (identitySubHomeomorph (fun x => x-(31/32 : ℝ) • G x) (15/16) (by norm_num) hG).trans
    (Homeomorph.smulOfNeZero (32/31 : ℝ) (by norm_num))

@[simp] theorem inverseDeformationHomeomorph_apply (G : EPlane → EPlane)
    (hG : LipschitzWith (15/16 : ℝ≥0) (fun x => x-(31/32 : ℝ) • G x)) (x : EPlane) :
    inverseDeformationHomeomorph G hG x = G x := by
  simp [inverseDeformationHomeomorph,smul_smul]

/-- No global bijectivity, properness, or target-tiling premise occurs here. -/
def inverseCoverHomeomorph {ι : Type*} (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j)
    (k i : ι → Fin 12) (a b : ι → EPlane) (G : EPlane → EPlane)
    (hchart : ∀ j x, x ∈ C j → affineEuclidean (k j) (i j) (a j) (b j) (G x) = x) :
    EPlane ≃ₜ EPlane :=
  inverseDeformationHomeomorph G
    (inverseCover_residual_lipschitz C hlocal hclosed hcover k i a b G hchart)

@[simp] theorem inverseCoverHomeomorph_apply {ι : Type*} (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j)
    (k i : ι → Fin 12) (a b : ι → EPlane) (G : EPlane → EPlane)
    (hchart : ∀ j x, x ∈ C j → affineEuclidean (k j) (i j) (a j) (b j) (G x) = x)
    (x : EPlane) : inverseCoverHomeomorph C hlocal hclosed hcover k i a b G hchart x = G x :=
  inverseDeformationHomeomorph_apply _ _ x

end
end SpectreGeometry.ReverseExistence
