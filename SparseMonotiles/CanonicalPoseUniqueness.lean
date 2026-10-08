module

public import SparseMonotiles.GlobalBodyAffine
public import SparseMonotiles.PyramidIsometryRigidityReference

@[expose] public section

/-!
# The fixed global key fields agree with every local canonical placement

The exact reference keys have trivial arbitrary-isometry stabilizers. Therefore
choosing a canonical frame before a generic ridge point is selected does not
change the finite halfspace fields used by a later isolated-key model.
-/
namespace SparseMonotiles

open Set

/-- A set with trivial isometry stabilizer has unique placed frames. -/
theorem isometryEquiv_eq_of_rigid_images {X : Type*} [MetricSpace X]
    (K : Set X) (hrigid : ∀ e : X ≃ᵢ X, e '' K = K → e = IsometryEquiv.refl X)
    (p q : X ≃ᵢ X) (h : p '' K = q '' K) : p = q := by
  let e := p.trans q.symm
  have he : e '' K = K := by
    calc
      e '' K = q.symm '' (p '' K) := by rw [Set.image_image]; rfl
      _ = q.symm '' (q '' K) := by rw [h]
      _ = K := by ext x; simp
  have heq := hrigid e he
  apply IsometryEquiv.ext
  intro x
  have hx := congrArg (fun f : X ≃ᵢ X => q (f x)) heq
  change q (q.symm (p x)) = q x at hx
  simpa only [q.apply_symm_apply] using hx

namespace Canonical

/-- Full Euclidean placement is determined by the actual five-dimensional solid. -/
theorem referenceSolid5_image_injective (p q : Point 5 ≃ᵢ Point 5)
    (h : p '' referenceSolid5 = q '' referenceSolid5) : p = q :=
  isometryEquiv_eq_of_rigid_images referenceSolid5 referenceSolid5_isometry_stabilizer p q h

theorem referenceSolid7_image_injective (p q : Point 7 ≃ᵢ Point 7)
    (h : p '' referenceSolid7 = q '' referenceSolid7) : p = q :=
  isometryEquiv_eq_of_rigid_images referenceSolid7 referenceSolid7_isometry_stabilizer p q h

theorem chosenKeyPose5_euclidean_eq (i : Fin keys5.length) (q : Contact.Pose 5)
    (hq : keySolid (keys5.get i) = q.euclidean '' referenceSolid5) :
    (chosenKeyPose5 i).euclidean = q.euclidean := by
  have h := referenceSolid5_image_injective (chosenKeyPose5 i).euclidean.toIsometryEquiv
    q.euclidean.toIsometryEquiv ((chosenKeyPose5_spec i).symm.trans hq)
  apply DFunLike.ext
  intro x
  exact congrArg (fun g : Point 5 ≃ᵢ Point 5 => g x) h

theorem chosenKeyPose7_euclidean_eq (i : Fin keys7.length) (q : Contact.Pose 7)
    (hq : keySolid (keys7.get i) = q.euclidean '' referenceSolid7) :
    (chosenKeyPose7 i).euclidean = q.euclidean := by
  have h := referenceSolid7_image_injective (chosenKeyPose7 i).euclidean.toIsometryEquiv
    q.euclidean.toIsometryEquiv ((chosenKeyPose7_spec i).symm.trans hq)
  apply DFunLike.ext
  intro x
  exact congrArg (fun g : Point 7 ≃ᵢ Point 7 => g x) h

theorem globalKeySlacks5_eq_local (i : Fin keys5.length) (q : Contact.Pose 5)
    (hq : keySolid (keys5.get i) = q.euclidean '' referenceSolid5) :
    globalKeySlacks5 i = posedHalfspaceSlack5 q := by
  funext j x
  change referenceHalfspaceSlack5 j ((chosenKeyPose5 i).euclidean.symm x) = _
  rw [chosenKeyPose5_euclidean_eq i q hq]
  rfl

theorem globalKeySlacks7_eq_local (i : Fin keys7.length) (q : Contact.Pose 7)
    (hq : keySolid (keys7.get i) = q.euclidean '' referenceSolid7) :
    globalKeySlacks7 i = posedHalfspaceSlack7 q := by
  funext j x
  change referenceHalfspaceSlack7 j ((chosenKeyPose7 i).euclidean.symm x) = _
  rw [chosenKeyPose7_euclidean_eq i q hq]
  rfl

end Canonical

open Canonical

theorem T5WorldAffineFields_eq_local_key (g : Point 5 ≃ᵢ Point 5)
    (i : Fin keys5.length) (q : Contact.Pose 5)
    (hq : keySolid (keys5.get i) = q.euclidean '' referenceSolid5)
    (j : PyramidHalfspaceIndex 4) (x : Point 5) :
    T5WorldAffineFields g (.inr (i,j)) x = posedHalfspaceSlack5 q j (g.symm x) := by
  rw [T5WorldAffineFields_apply]
  change globalKeySlacks5 i j (g.symm x) = _
  rw [globalKeySlacks5_eq_local i q hq]

theorem T7WorldAffineFields_eq_local_key (g : Point 7 ≃ᵢ Point 7)
    (i : Fin keys7.length) (q : Contact.Pose 7)
    (hq : keySolid (keys7.get i) = q.euclidean '' referenceSolid7)
    (j : PyramidHalfspaceIndex 6) (x : Point 7) :
    T7WorldAffineFields g (.inr (i,j)) x = posedHalfspaceSlack7 q j (g.symm x) := by
  rw [T7WorldAffineFields_apply]
  change globalKeySlacks7 i j (g.symm x) = _
  rw [globalKeySlacks7_eq_local i q hq]

#print axioms Canonical.chosenKeyPose5_euclidean_eq
#print axioms Canonical.chosenKeyPose7_euclidean_eq
#print axioms T5WorldAffineFields_eq_local_key
#print axioms T7WorldAffineFields_eq_local_key

end SparseMonotiles
