module
public import closure_analysis.CoarseHoles
@[expose] public section
namespace RegisteredPrime

/-- Incoming geometric support already determines its sign mask. -/
theorem incoming_support_negative_mask {p : Nat} (e : Pose p) (A : Mask p)
    (hin : IncomingSupport e A) : ∀ i, e.frame.negative i = A i := by
  intro i
  have hh := congrFun hin.2 i
  rw [hole_from_box, congrFun hin.1 i] at hh
  cases hn : e.frame.negative i <;> cases ha : A i <;>
    simp [bit, hn, ha] at hh ⊢ <;> omega

/-- Reversing an incoming-support contact puts the owner's box at ones. -/
theorem incoming_support_inverse_box {p : Nat} (e : Pose p) (A : Mask p)
    (hin : IncomingSupport e A) : boxLower e.inv = (fun _ => 1) := by
  funext i
  have hn := incoming_support_negative_mask e A hin (e.frame.inverse i)
  have hb := congrFun hin.1 (e.frame.inverse i)
  simp only [boxLower] at hb
  simp only [boxLower, Pose.inv, RegisteredFrame.inv, RegisteredFrame.linear,
    RegisteredFrame.sign]
  simp only [hn] at hb ⊢
  cases ha : A (e.frame.inverse i) <;> simp [bit, ha] at hb ⊢ <;> omega

/-- The original root owns an incoming tile's hole, hence is the outgoing
owner after normalization at that tile. -/
theorem incoming_support_inverse_owns (P : Parameters) (e : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (hin : IncomingSupport e A) :
    Occupies e.inv (fun _ => 1) := by
  apply (occupies_comp_cell e e.inv (fun _ => 1)).mp
  rw [Pose.comp_inv]
  change Occupies (identityPose P.p) (hole e)
  rw [hin.2]
  exact root_owns_role A hA

theorem disjoint_root_inverse {p : Nat} (e : Pose p)
    (hd : Disjoint (identityPose p) e) : Disjoint (identityPose p) e.inv := by
  intro c ⟨hroot, hinv⟩
  have he : Occupies e (e.cell c) := by
    have h := (occupies_comp_cell e (identityPose p) c).mpr hroot
    rwa [Pose.comp_identity] at h
  have hi : Occupies (identityPose p) (e.cell c) := by
    have h := (occupies_comp_cell e e.inv c).mpr hinv
    rwa [Pose.comp_inv] at h
  exact hd (e.cell c) ⟨hi, he⟩

/-- Normalize reverse fine-contact legality at the second coarse parent. -/
theorem reverse_child_recognition_normalized (P : Parameters) (e : Pose P.p)
    (hl : WeakRecognition.ChildRecognition P (doubleAnchor e) (identityPose P.p)) :
    WeakRecognition.ChildRecognition P (identityPose P.p) (doubleAnchor e.inv) := by
  have h := WeakRecognition.ChildRecognition.reframe P (doubleAnchor e).inv
    (doubleAnchor e) (identityPose P.p) hl
  rw [Pose.inv_comp, Pose.comp_identity] at h
  simpa only [← doubleAnchor_inv] using h

/-- Exact outgoing seed classification on the inverse implies the exact
marked incoming pose, using only the specified geometric support. -/
theorem outgoing_inverse_seed_incoming_pose (P : Parameters) (e : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (hin : IncomingSupport e A)
    (hout : OutgoingSeed P e.inv) : e = incomingPose P A hA := by
  obtain ⟨B, hB, hseed⟩ := hout
  have he := congrArg Pose.inv hseed
  rw [Pose.inv_inv, seed_inverse_incoming] at he
  have hs : IncomingSupport e (scalarRole P B) := by
    rw [he]
    exact incoming_support P _ _
  have hrole := IncomingSupport.role_unique hin hs
  simpa only [hrole] using he

/-- Local exact-pose incoming preservation, using actual reverse child
recognition. No coarse E-legality or parent recognition is assumed. -/
theorem coarse_incoming_pose_of_child_recognition (P : Parameters) (e : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (hin : IncomingSupport e A)
    (hd : Disjoint (identityPose P.p) e)
    (hl : WeakRecognition.ChildRecognition P (doubleAnchor e) (identityPose P.p)) :
    e = incomingPose P A hA := by
  apply outgoing_inverse_seed_incoming_pose P e A hA hin
  exact coarse_outgoing_seed_of_child_recognition P e.inv
    (incoming_support_inverse_box e A hin)
    (incoming_support_inverse_owns P e A hA hin)
    (disjoint_root_inverse e hd)
    (reverse_child_recognition_normalized P e hl)

end RegisteredPrime
