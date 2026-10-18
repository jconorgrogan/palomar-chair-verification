module

public import SpectreGeometry.PolygonProductBoundaryNormals
public import Mathlib.Analysis.Normed.Affine.Isometry

@[expose] public section


/-! The actual 56-site orthonormal frames of `even_family/even_4d_recipe.json`.

The index is (zero-based factor, edge, polarity bit); false means +1, true -1.
The fourth frame vector is the recipe's outward normal, independent of the
polarity bit. It is the negative of the existing inward native normal.

The recipe source has SHA-256
`e5756588e23ac658c352abae3a1f911919a0042c8ddfe90c872d736edfd426f2`;
its canonical payload digest is
`c428a05ff09b1f0e7d695f3eb546628cb2a475e48eaf424e3ddafdf4fd7b113e`.
The external provenance audit checks the exact rational-quadratic source rows.
This module does not assert collar containment, body membership, local halfspace
agreement, or a binding to a keyed body. -/
namespace SpectreGeometry
noncomputable section

/-- Zero-based factor, edge, and polarity bit. False is the positive JSON row. -/
abbrev ProductKeySite := Fin 2 × Fin 14 × Bool

theorem productKeySite_card : Fintype.card ProductKeySite = 56 := by decide

/-- The zero-based JSON cap row: factor first, edge next, then +1 and -1. -/
def productKeyJsonIndex (s : ProductKeySite) : Fin 56 :=
  ⟨28 * s.1.val + 2 * s.2.1.val + (if s.2.2 then 1 else 0), by
    have hb := s.1.isLt
    have hi := s.2.1.isLt
    split <;> omega⟩

def productKeySiteAtIndex (n : Fin 56) : ProductKeySite :=
  (⟨n.val / 28, by omega⟩, ⟨n.val % 28 / 2, by omega⟩, n.val % 2 == 1)

/-- Explicit bijection, preserving the source JSON cap ordering. -/
def productKeyIndexEquiv : ProductKeySite ≃ Fin 56 where
  toFun := productKeyJsonIndex
  invFun := productKeySiteAtIndex
  left_inv := by decide
  right_inv := by decide

/-- Real polarity, with false = +1 and true = -1. -/
def productKeySign (s : ProductKeySite) : ℝ := if s.2.2 then -1 else 1

/-- The source's signed label, τ times the one-based active factor. -/
def productKeySignedLabel (s : ProductKeySite) : ℤ :=
  (if s.2.2 then -1 else 1) * (s.1.val + 1)

theorem productKeySignedLabel_ne_zero (s : ProductKeySite) :
    productKeySignedLabel s ≠ 0 := by
  rcases s with ⟨b, i, e⟩
  fin_cases b <;> cases e <;> norm_num [productKeySignedLabel]

theorem productKeySignedLabel_real (s : ProductKeySite) :
    (productKeySignedLabel s : ℝ) = productKeySign s * (s.1.val + 1) := by
  rcases s with ⟨b, i, e⟩
  cases e <;> simp [productKeySignedLabel, productKeySign]

def productKeyEta : ℝ := 1 / 40000
def productKeyRho : ℝ := 1 / 40000
def productKeyN : ℕ := 4357
def productKeyPrimePairs : Fin 3 → ℕ × ℕ := ![(3,5),(7,11),(13,17)]

/-- False chooses the negative-side denominator; true the positive-side one. -/
def productKeyPrime (j : Fin 3) (side : Bool) : ℕ :=
  if side then (productKeyPrimePairs j).2 else (productKeyPrimePairs j).1

theorem productKey_constants :
    productKeyEta = 1 / 40000 ∧ productKeyRho = 1 / 40000 ∧
    productKeyN = 4357 ∧ productKeyPrimePairs = ![(3,5),(7,11),(13,17)] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The active edge point is at parameter 1/4 or 3/4, exactly as in the source. -/
def productKeyActiveCenter (s : ProductKeySite) : RealPoint :=
  realVertex s.2.1 + (1 / 2 - productKeySign s / 4) • realEdge s.2.1

def productKeyCenter (s : ProductKeySite) : EFour :=
  if s.1 = 0 then productCoordinates (productKeyActiveCenter s, (1/2,1/2))
  else productCoordinates ((1/2,1/2), productKeyActiveCenter s)

theorem productKeyCenter_left (i : Fin 14) (e : Bool) :
    productKeyCenter (0,i,e) =
      productCoordinates (realVertex i + (1/2 - productKeySign (0,i,e)/4) • realEdge i,
        (1/2,1/2)) := by simp [productKeyCenter, productKeyActiveCenter]

theorem productKeyCenter_right (i : Fin 14) (e : Bool) :
    productKeyCenter (1,i,e) =
      productCoordinates ((1/2,1/2),
        realVertex i + (1/2 - productKeySign (1,i,e)/4) • realEdge i) := by
  simp [productKeyCenter, productKeyActiveCenter]

/-- Three tangent columns: signed active edge, then the two positive passive axes. -/
def productKeyTangent (s : ProductKeySite) : Fin 3 → EFour :=
  if s.1 = 0 then
    ![leftNormalMap (productKeySign s • realEdge s.2.1),
      rightNormalMap (1,0), rightNormalMap (0,1)]
  else
    ![rightNormalMap (productKeySign s • realEdge s.2.1),
      leftNormalMap (1,0), leftNormalMap (0,1)]

/-- The clockwise edge normal (edge_y,-edge_x), with no polarity multiplier. -/
def productKeyOutwardNormal (s : ProductKeySite) : EFour :=
  if s.1 = 0 then leftNormalMap ((realEdge s.2.1).2, -(realEdge s.2.1).1)
  else rightNormalMap ((realEdge s.2.1).2, -(realEdge s.2.1).1)

theorem productKeyOutwardNormal_eq_negative_native (s : ProductKeySite) :
    productKeyOutwardNormal s =
      if s.1 = 0 then -nativeLeftNormal s.2.1 else -nativeRightNormal s.2.1 := by
  rcases s with ⟨b, i, e⟩
  fin_cases b <;> ext k <;> fin_cases k <;>
    simp [productKeyOutwardNormal, nativeLeftNormal, nativeRightNormal,
      nativeEdgeNormal, leftNormalMap, rightNormalMap, productCoordinateLinearEquiv]

theorem productKeyOutwardNormal_polarity_independent (b : Fin 2) (i : Fin 14) :
    productKeyOutwardNormal (b,i,false) = productKeyOutwardNormal (b,i,true) := rfl

/-- The three tangent columns followed by the independent outward normal. -/
def productKeyFrame (s : ProductKeySite) : Fin 4 → EFour :=
  ![productKeyTangent s 0, productKeyTangent s 1, productKeyTangent s 2,
    productKeyOutwardNormal s]

@[simp] theorem productKeyFrame_tangent (s : ProductKeySite) (j : Fin 3) :
    productKeyFrame s j.castSucc = productKeyTangent s j := by
  fin_cases j <;> rfl

@[simp] theorem productKeyFrame_normal (s : ProductKeySite) :
    productKeyFrame s 3 = productKeyOutwardNormal s := rfl

/-- Every one of the 16 Gram entries for each of the 56 source frames. -/
theorem productKeyFrame_inner (s : ProductKeySite) (j k : Fin 4) :
    inner ℝ (productKeyFrame s j) (productKeyFrame s k) = if j = k then 1 else 0 := by
  rcases s with ⟨b, i, e⟩
  have hu := real_edges_unit_squared i
  simp only [RealPoint.dot] at hu
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  fin_cases b <;> cases e <;> fin_cases j <;> fin_cases k <;>
    simp [productKeyFrame, productKeyTangent, productKeyOutwardNormal, productKeySign,
      leftNormalMap, rightNormalMap, productCoordinateLinearEquiv,
      PiLp.inner_apply, Fin.sum_univ_succ] <;> nlinarith [hu]

theorem productKeyFrame_orthonormal (s : ProductKeySite) :
    Orthonormal ℝ (productKeyFrame s) :=
  orthonormal_iff_ite.mpr (productKeyFrame_inner s)

theorem productKeyTangent_norm (s : ProductKeySite) (j : Fin 3) :
    ‖productKeyTangent s j‖ = 1 := by
  simpa using (productKeyFrame_orthonormal s).norm_eq_one j.castSucc

theorem productKeyTangent_inner (s : ProductKeySite) (j k : Fin 3) :
    inner ℝ (productKeyTangent s j) (productKeyTangent s k) = if j = k then 1 else 0 := by
  simpa using productKeyFrame_inner s j.castSucc k.castSucc

theorem productKeyOutwardNormal_norm (s : ProductKeySite) :
    ‖productKeyOutwardNormal s‖ = 1 := by
  simpa using (productKeyFrame_orthonormal s).norm_eq_one 3

theorem productKeyOutwardNormal_inner_tangent (s : ProductKeySite) (j : Fin 3) :
    inner ℝ (productKeyOutwardNormal s) (productKeyTangent s j) = 0 := by
  have h := productKeyFrame_inner s 3 j.castSucc
  fin_cases j <;> simpa [productKeyFrame] using h

/-- The frame is an actual basis of the ambient Euclidean four-space. -/
def productKeyBasis (s : ProductKeySite) : Module.Basis (Fin 4) ℝ EFour :=
  basisOfOrthonormalOfCardEqFinrank (productKeyFrame_orthonormal s) (by simp [EFour])

@[simp] theorem productKeyBasis_apply (s : ProductKeySite) (j : Fin 4) :
    productKeyBasis s j = productKeyFrame s j := by
  simp [productKeyBasis]

def productKeyOrthonormalBasis (s : ProductKeySite) : OrthonormalBasis (Fin 4) ℝ EFour :=
  (productKeyBasis s).toOrthonormalBasis (by simpa [productKeyBasis] using productKeyFrame_orthonormal s)

@[simp] theorem productKeyOrthonormalBasis_apply (s : ProductKeySite) (j : Fin 4) :
    productKeyOrthonormalBasis s j = productKeyFrame s j := by
  simp [productKeyOrthonormalBasis]

/-- Reference coordinates (three tangent coordinates, outward height) to space. -/
def productKeyLinearIsometry (s : ProductKeySite) : EFour ≃ₗᵢ[ℝ] EFour :=
  (productKeyOrthonormalBasis s).repr.symm

theorem productKeyLinearIsometry_apply (s : ProductKeySite) (w : EFour) :
    productKeyLinearIsometry s w = ∑ j : Fin 4, w j • productKeyFrame s j := by
  simpa [productKeyLinearIsometry] using
    ((productKeyOrthonormalBasis s).sum_repr_symm w).symm

/-- The actual affine isometry anchored at the JSON site's center. -/
def productKeyAffineIsometry (s : ProductKeySite) : EFour ≃ᵃⁱ[ℝ] EFour :=
  (productKeyLinearIsometry s).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ EFour (productKeyCenter s))

theorem productKeyAffineIsometry_apply (s : ProductKeySite) (w : EFour) :
    productKeyAffineIsometry s w =
      productKeyCenter s + ∑ j : Fin 4, w j • productKeyFrame s j := by
  change productKeyCenter s + productKeyLinearIsometry s w = _
  rw [productKeyLinearIsometry_apply]

theorem productKeyAffineIsometry_zero (s : ProductKeySite) :
    productKeyAffineIsometry s 0 = productKeyCenter s := by
  simp [productKeyAffineIsometry_apply]

end
end SpectreGeometry
