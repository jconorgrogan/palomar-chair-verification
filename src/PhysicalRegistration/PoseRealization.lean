module

public import PhysicalRegistration.RegisteredWorldBridge
public import RegisteredPrime.PoseAlgebra

@[expose] public section

/-! Every original registered hierarchy pose has a literal Euclidean isometry.
The representation is faithful and respects the original row convention. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- Turn the original pair of inverse index maps into an actual permutation. -/
def rowPermutation {m : ℕ} (F : RegisteredPrime.RegisteredFrame (m+1)) :
    Equiv.Perm (Fin (m+1)) where
  toFun := F.perm
  invFun := F.inverse
  left_inv := F.left_inverse
  right_inv := F.right_inverse

/-- The signed row action, as an actual orthogonal linear equivalence. -/
def registeredFrameIsometry {m : ℕ} (F : RegisteredPrime.RegisteredFrame (m+1)) :
    Space m ≃ₗᵢ[ℝ] Space m :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (rowPermutation F).symm).trans
    (LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin (m+1) =>
      if F.negative i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ))

@[simp] theorem registeredFrameIsometry_apply {m : ℕ}
    (F : RegisteredPrime.RegisteredFrame (m+1)) (x : Space m) (i : Fin (m+1)) :
    registeredFrameIsometry F x i = (F.sign i : ℝ) * x (F.perm i) := by
  cases hi : F.negative i <;>
    simp [registeredFrameIsometry, rowPermutation, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft', RegisteredPrime.RegisteredFrame.sign, hi]

def integerPoint {m : ℕ} (z : LatticeIndex m) : Space m :=
  WithLp.toLp 2 (fun i => (z i : ℝ))

/-- The exact Euclidean isometry realizing the hierarchy pose. -/
def poseIsometry {m : ℕ} (q : RegisteredPrime.Pose (m+1)) : Space m ≃ᵢ Space m :=
  (registeredFrameIsometry q.frame).toIsometryEquiv.trans
    (IsometryEquiv.vaddConst (integerPoint q.anchor))

@[simp] theorem poseIsometry_apply {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (x : Space m) (i : Fin (m+1)) :
    poseIsometry q x i = (q.frame.sign i : ℝ) * x (q.frame.perm i) + (q.anchor i : ℝ) := by
  change registeredFrameIsometry q.frame x i + (q.anchor i : ℝ) = _
  rw [registeredFrameIsometry_apply]

theorem poseIsometry_realizes {m : ℕ} (q : RegisteredPrime.Pose (m+1)) :
    RegisteredPoseRealizes q (poseIsometry q) := poseIsometry_apply q

/-- A chosen physical representative is exactly the realized pose, not merely
set-congruent to it. -/
theorem RegisteredPoseRealizes.eq_poseIsometry {m : ℕ}
    {q : RegisteredPrime.Pose (m+1)} {e : Space m ≃ᵢ Space m}
    (h : RegisteredPoseRealizes q e) : e = poseIsometry q := by
  apply IsometryEquiv.ext
  intro x
  ext i
  rw [h, poseIsometry_apply]

theorem registeredPoseRealizes_unique {m : ℕ}
    {q r : RegisteredPrime.Pose (m+1)} {e : Space m ≃ᵢ Space m}
    (hq : RegisteredPoseRealizes q e) (hr : RegisteredPoseRealizes r e) : q = r := by
  have hcoords (x : Space m) (i : Fin (m+1)) := (hq x i).symm.trans (hr x i)
  have ha : q.anchor = r.anchor := by
    funext i
    have h := hcoords 0 i
    simp only [PiLp.zero_apply, mul_zero, zero_add] at h
    exact_mod_cast h
  have hp : q.frame.perm = r.frame.perm := by
    funext i
    by_contra hne
    have h := hcoords (EuclideanSpace.single (q.frame.perm i) 1) i
    rw [ha] at h
    cases hneg : q.frame.negative i <;>
      simp [Ne.symm hne,
        RegisteredPrime.RegisteredFrame.sign, hneg] at h
  have hn : q.frame.negative = r.frame.negative := by
    funext i
    let x : Space m := WithLp.toLp 2 (fun _ => (1 : ℝ))
    have h := hcoords x i
    rw [ha] at h
    cases hqneg : q.frame.negative i <;> cases hrneg : r.frame.negative i <;>
      simp [x, RegisteredPrime.RegisteredFrame.sign, hqneg, hrneg] at h ⊢ <;> norm_num at h
  apply RegisteredPrime.Pose.Same.eq
  exact ⟨fun i => congrFun hp i, fun i => congrFun hn i, fun i => congrFun ha i⟩

theorem poseIsometry_injective {m : ℕ} :
    Function.Injective (poseIsometry (m := m)) := by
  intro q r h
  apply registeredPoseRealizes_unique (poseIsometry_realizes q)
  rw [h]
  exact poseIsometry_realizes r

/-- Composition follows the hierarchy's exact row convention. -/
theorem poseIsometry_comp {m : ℕ} (q r : RegisteredPrime.Pose (m+1)) :
    poseIsometry (q.comp r) = (poseIsometry r).trans (poseIsometry q) := by
  apply IsometryEquiv.ext
  intro x
  ext i
  simp only [IsometryEquiv.trans_apply, poseIsometry_apply]
  change ((q.frame.comp r.frame).sign i : ℝ) * x (r.frame.perm (q.frame.perm i)) +
      ((q.anchor i + q.frame.linear r.anchor i : ℤ) : ℝ) =
    (q.frame.sign i : ℝ) * ((r.frame.sign (q.frame.perm i) : ℝ) *
      x (r.frame.perm (q.frame.perm i)) + (r.anchor (q.frame.perm i) : ℝ)) + (q.anchor i : ℝ)
  rw [RegisteredPrime.RegisteredFrame.comp_sign, Int.cast_mul, Int.cast_add]
  simp only [RegisteredPrime.RegisteredFrame.linear, Int.cast_mul]
  ring

@[simp] theorem poseIsometry_identity {m : ℕ} :
    poseIsometry (RegisteredPrime.identityPose (m+1)) = IsometryEquiv.refl (Space m) := by
  apply IsometryEquiv.ext
  intro x
  ext i
  change poseIsometry (RegisteredPrime.identityPose (m+1)) x i = x i
  simp [poseIsometry_apply, RegisteredPrime.identityPose, RegisteredPrime.RegisteredFrame.sign]

end
end PhysicalRegistration.NativeChair
