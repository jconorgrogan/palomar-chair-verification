module

public import SparseMonotiles.GlobalBodyHalfspaceFormula
public import Mathlib.Analysis.Normed.Affine.MazurUlam

@[expose] public section

/-!
# Fixed affine plane families in arbitrary physical tile frames

Every global body slack is represented by a genuine real affine map. The
Mazur--Ulam equivalence transports it through every isometry allowed by the
physical tiling model, without an integer-registration hypothesis.
-/
namespace SparseMonotiles

open Set

noncomputable def coordinateLinearMap {d : ℕ} (i : Fin d) : Point d →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def carrierSlackAffine {d : ℕ} (j : CarrierHalfspaceIndex d) :
    Point d →ᵃ[ℝ] ℝ :=
  if j.2 = 0 then (coordinateLinearMap j.1).toAffineMap
  else if j.2 = 1 then AffineMap.const ℝ (Point d) 2 - (coordinateLinearMap j.1).toAffineMap
  else AffineMap.const ℝ (Point d) 1 - (coordinateLinearMap j.1).toAffineMap

theorem carrierSlackAffine_apply {d : ℕ} (j : CarrierHalfspaceIndex d) (x : Point d) :
    carrierSlackAffine j x = carrierHalfspaceSlack j x := by
  by_cases h0 : j.2 = 0
  · simp [carrierSlackAffine, carrierHalfspaceSlack, h0, coordinateLinearMap] <;> rfl
  · by_cases h1 : j.2 = 1 <;>
      simp [carrierSlackAffine, carrierHalfspaceSlack, h0, h1, coordinateLinearMap] <;> rfl

noncomputable def keyPyramidSlackAffine {n : ℕ} (k : KeyData (n+1))
    (j : PyramidHalfspaceIndex n) : Point (n+1) →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (Point (n+1)) (keyPyramidHalfspaceBound k j) -
    (keyPyramidHalfspaceNormal k j).toAffineMap

theorem keyPyramidSlackAffine_apply {n : ℕ} (k : KeyData (n+1))
    (j : PyramidHalfspaceIndex n) (x : Point (n+1)) :
    keyPyramidSlackAffine k j x = keyPyramidHalfspaceSlack k j x := rfl

namespace Canonical

noncomputable def posedSlackAffine5 (p : Contact.Pose 5) (j : PyramidHalfspaceIndex 4) :
    Point 5 →ᵃ[ℝ] ℝ :=
  (keyPyramidSlackAffine ((referenceBox5 true).toKeyData 19200) j).comp
    p.euclidean.symm.toAffineEquiv.toAffineMap

noncomputable def posedSlackAffine7 (p : Contact.Pose 7) (j : PyramidHalfspaceIndex 6) :
    Point 7 →ᵃ[ℝ] ℝ :=
  (keyPyramidSlackAffine ((referenceBox7 true).toKeyData 188160) j).comp
    p.euclidean.symm.toAffineEquiv.toAffineMap

theorem posedSlackAffine5_apply (p : Contact.Pose 5) (j : PyramidHalfspaceIndex 4)
    (x : Point 5) : posedSlackAffine5 p j x = posedHalfspaceSlack5 p j x := rfl

theorem posedSlackAffine7_apply (p : Contact.Pose 7) (j : PyramidHalfspaceIndex 6)
    (x : Point 7) : posedSlackAffine7 p j x = posedHalfspaceSlack7 p j x := rfl

end Canonical

open Canonical

noncomputable def T5GlobalAffineFields :
    GlobalBodyHalfspaceIndex keys5 (PyramidHalfspaceIndex 4) → Point 5 →ᵃ[ℝ] ℝ
  | .inl j => carrierSlackAffine j
  | .inr (i,j) => posedSlackAffine5 (chosenKeyPose5 i) j

noncomputable def T7GlobalAffineFields :
    GlobalBodyHalfspaceIndex keys7 (PyramidHalfspaceIndex 6) → Point 7 →ᵃ[ℝ] ℝ
  | .inl j => carrierSlackAffine j
  | .inr (i,j) => posedSlackAffine7 (chosenKeyPose7 i) j

theorem T5GlobalAffineFields_apply (j) (x : Point 5) :
    T5GlobalAffineFields j x = T5GlobalSlacks j x := by
  cases j with
  | inl j => exact carrierSlackAffine_apply j x
  | inr ij => rfl

theorem T7GlobalAffineFields_apply (j) (x : Point 7) :
    T7GlobalAffineFields j x = T7GlobalSlacks j x := by
  cases j with
  | inl j => exact carrierSlackAffine_apply j x
  | inr ij => rfl

/-- A physical frame is arbitrary; the affine conversion is a theorem of mathlib. -/
noncomputable def T5WorldAffineFields (g : Point 5 ≃ᵢ Point 5)
    (j : GlobalBodyHalfspaceIndex keys5 (PyramidHalfspaceIndex 4)) : Point 5 →ᵃ[ℝ] ℝ :=
  (T5GlobalAffineFields j).comp g.symm.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap

noncomputable def T7WorldAffineFields (g : Point 7 ≃ᵢ Point 7)
    (j : GlobalBodyHalfspaceIndex keys7 (PyramidHalfspaceIndex 6)) : Point 7 →ᵃ[ℝ] ℝ :=
  (T7GlobalAffineFields j).comp g.symm.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap

theorem T5WorldAffineFields_apply (g : Point 5 ≃ᵢ Point 5) (j) (x : Point 5) :
    T5WorldAffineFields g j x = T5GlobalSlacks j (g.symm x) :=
  T5GlobalAffineFields_apply j (g.symm x)

theorem T7WorldAffineFields_apply (g : Point 7 ≃ᵢ Point 7) (j) (x : Point 7) :
    T7WorldAffineFields g j x = T7GlobalSlacks j (g.symm x) :=
  T7GlobalAffineFields_apply j (g.symm x)

/-- Finite Boolean syntax commutes with an arbitrary bijective physical frame. -/
theorem image_halfspaceFormula_region {d : ℕ} {ι : Type*}
    (g : Point d ≃ᵢ Point d) (f : ι → Point d → ℝ) (A : HalfspaceFormula ι) :
    g '' A.region f = A.region (fun j x => f j (g.symm x)) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change A.eval (fun j => 0 ≤ f j (g.symm (g y)))
    rw [g.symm_apply_apply]
    exact hy
  · intro hx
    exact ⟨g.symm x,hx,g.apply_symm_apply x⟩

theorem isometry_image_closure {d : ℕ} (g : Point d ≃ᵢ Point d) (S : Set (Point d)) :
    g '' closure S = closure (g '' S) := by
  rw [show (g : Point d → Point d) = g.toHomeomorph from rfl]
  exact g.toHomeomorph.image_closure S

theorem T5_copy_global_halfspace_formula (g : Point 5 ≃ᵢ Point 5) :
    g '' T5 = closure ((globalBodyFormula keys5 (PyramidHalfspaceIndex 4)).region
      (fun j x => T5GlobalSlacks j (g.symm x))) := by
  rw [T5_global_halfspace_formula, isometry_image_closure]
  rw [image_halfspaceFormula_region]

theorem T7_copy_global_halfspace_formula (g : Point 7 ≃ᵢ Point 7) :
    g '' T7 = closure ((globalBodyFormula keys7 (PyramidHalfspaceIndex 6)).region
      (fun j x => T7GlobalSlacks j (g.symm x))) := by
  rw [T7_global_halfspace_formula, isometry_image_closure]
  rw [image_halfspaceFormula_region]

#print axioms T5WorldAffineFields_apply
#print axioms T7WorldAffineFields_apply
#print axioms T5_copy_global_halfspace_formula
#print axioms T7_copy_global_halfspace_formula

end SparseMonotiles
