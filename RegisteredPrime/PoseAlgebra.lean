module
public import RegisteredPrime.CentralHoleOwner
@[expose] public section
namespace RegisteredPrime
@[simp] theorem RegisteredFrame.comp_sign {p : Nat} (F G : RegisteredFrame p) (i : Fin p) :
    (F.comp G).sign i = F.sign i * G.sign (F.perm i) := by
  simp only [RegisteredFrame.comp, RegisteredFrame.sign]
  by_cases hf : F.negative i = true <;> by_cases hg : G.negative (F.perm i) = true <;>
    simp [hf, hg]
theorem Pose.comp_assoc {p : Nat} (q r s : Pose p) : (q.comp r).comp s = q.comp (r.comp s) := by
  apply Pose.Same.eq
  constructor
  · intro i
    rfl
  constructor
  · intro i
    change xor (xor (q.frame.negative i) (r.frame.negative (q.frame.perm i)))
        (s.frame.negative (r.frame.perm (q.frame.perm i))) =
      xor (q.frame.negative i) (xor (r.frame.negative (q.frame.perm i))
        (s.frame.negative (r.frame.perm (q.frame.perm i))))
    exact Bool.xor_assoc _ _ _
  · intro i
    change (q.anchor i + q.frame.sign i * r.anchor (q.frame.perm i)) +
        (q.frame.comp r.frame).sign i * s.anchor (r.frame.perm (q.frame.perm i)) =
      q.anchor i + q.frame.sign i *
        (r.anchor (q.frame.perm i) + r.frame.sign (q.frame.perm i) *
          s.anchor (r.frame.perm (q.frame.perm i)))
    rw [RegisteredFrame.comp_sign]
    grind
@[simp] theorem Pose.comp_identity {p : Nat} (q : Pose p) : q.comp (identityPose p) = q := by
  apply Pose.Same.eq
  constructor
  · intro i
    rfl
  constructor
  · intro i
    simp [Pose.comp, RegisteredFrame.comp, identityPose]
  · intro i
    simp [Pose.comp, RegisteredFrame.linear, identityPose]
@[simp] theorem Pose.identity_comp {p : Nat} (q : Pose p) : (identityPose p).comp q = q := by
  apply Pose.Same.eq
  constructor
  · intro i
    rfl
  constructor
  · intro i
    simp [Pose.comp, RegisteredFrame.comp, identityPose]
  · intro i
    simp [Pose.comp, RegisteredFrame.linear, RegisteredFrame.sign, identityPose]
@[simp] theorem Pose.inv_comp {p : Nat} (q : Pose p) : q.inv.comp q = identityPose p := by
  apply Pose.Same.eq
  constructor
  · intro i
    exact q.frame.right_inverse i
  constructor
  · intro i
    simp [Pose.comp, Pose.inv, RegisteredFrame.comp, RegisteredFrame.inv, identityPose]
  · intro i
    simp [Pose.comp, Pose.inv, RegisteredFrame.linear, identityPose]
    omega
@[simp] theorem Pose.comp_inv {p : Nat} (q : Pose p) : q.comp q.inv = identityPose p := by
  apply Pose.Same.eq
  constructor
  · intro i
    exact q.frame.left_inverse i
  constructor
  · intro i
    simp [Pose.comp, Pose.inv, RegisteredFrame.comp, RegisteredFrame.inv,
      identityPose, q.frame.left_inverse]
  · intro i
    simp only [Pose.comp, Pose.inv, RegisteredFrame.linear, RegisteredFrame.sign,
      RegisteredFrame.inv, identityPose, q.frame.left_inverse]
    by_cases hn : q.frame.negative i = true <;> simp [hn] <;> omega
theorem Pose.inverse_unique {p : Nat} (q r : Pose p) (h : q.comp r = identityPose p) : r = q.inv := by
  have he := congrArg (fun s => q.inv.comp s) h
  rw [← Pose.comp_assoc, Pose.inv_comp, Pose.identity_comp, Pose.comp_identity] at he
  exact he
@[simp] theorem Pose.inv_compose {p : Nat} (q r : Pose p) :
    (q.comp r).inv = r.inv.comp q.inv := by
  symm
  apply Pose.inverse_unique
  rw [Pose.comp_assoc, ← Pose.comp_assoc r, Pose.comp_inv, Pose.identity_comp, Pose.comp_inv]
@[simp] theorem Pose.inv_inv {p : Nat} (q : Pose p) : q.inv.inv = q := by
  symm
  exact Pose.inverse_unique q.inv q (Pose.inv_comp q)
theorem Pose.relative_left_cancel {p : Nat} (q r s : Pose p) :
    (q.comp r).relative (q.comp s) = r.relative s := by
  simp only [Pose.relative, Pose.inv_compose]
  rw [Pose.comp_assoc, ← Pose.comp_assoc q.inv, Pose.inv_comp, Pose.identity_comp]
@[simp] theorem Pose.comp_relative {p : Nat} (q r : Pose p) : q.comp (q.relative r) = r := by
  unfold Pose.relative
  rw [← Pose.comp_assoc, Pose.comp_inv, Pose.identity_comp]
theorem doubleAnchor_comp {p : Nat} (q r : Pose p) :
    doubleAnchor (q.comp r) = (doubleAnchor q).comp (doubleAnchor r) := by
  apply Pose.Same.eq
  constructor
  · intro i
    rfl
  constructor
  · intro i
    rfl
  · intro i
    simp only [doubleAnchor, Pose.comp, RegisteredFrame.linear]
    grind
@[simp] theorem doubleAnchor_identity (p : Nat) : doubleAnchor (identityPose p) = identityPose p := by
  apply Pose.Same.eq
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
theorem doubleAnchor_inv {p : Nat} (q : Pose p) : doubleAnchor q.inv = (doubleAnchor q).inv := by
  apply Pose.inverse_unique
  rw [← doubleAnchor_comp, Pose.comp_inv, doubleAnchor_identity]
theorem refine_comp (P : Parameters) (q r : Pose P.p) (a : Role P.p) :
    refine P (q.comp r) a = (doubleAnchor q).comp (refine P r a) := by
  change (doubleAnchor (q.comp r)).comp (arithmeticChild P a) =
    (doubleAnchor q).comp ((doubleAnchor r).comp (arithmeticChild P a))
  rw [doubleAnchor_comp, Pose.comp_assoc]
theorem refine_relative (P : Parameters) (q r : Pose P.p) (a b : Role P.p) :
    (refine P q a).relative (refine P r b) =
      (arithmeticChild P a).relative (refine P (q.relative r) b) := by
  have he : r = q.comp (q.relative r) := (Pose.comp_relative q r).symm
  have her := congrArg (fun s => refine P s b) he
  rw [refine_comp] at her
  rw [her]
  change ((doubleAnchor q).comp (arithmeticChild P a)).relative
      ((doubleAnchor q).comp (refine P (q.relative r) b)) = _
  rw [Pose.relative_left_cancel]
end RegisteredPrime
