module
public import RegisteredPrime.GeneratedWallGeometry
@[expose] public section
namespace RegisteredPrime
@[simp] theorem child_central_negative (P : Parameters) (i : Fin P.p) :
    (arithmeticChild P .central).frame.negative i = false := rfl
@[simp] theorem child_central_anchor (P : Parameters) (i : Fin P.p) :
    (arithmeticChild P .central).anchor i = 1 := rfl
@[simp] theorem child_outer_negative (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (i : Fin P.p) : (arithmeticChild P (.outer A hA)).frame.negative i = A i :=
  outerFrame_neg P A i
@[simp] theorem child_outer_anchor (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (i : Fin P.p) : (arithmeticChild P (.outer A hA)).anchor i = if A i then 4 else 0 := rfl
noncomputable def incomingRole (P : Parameters) (A : Mask P.p) : Mask P.p :=
  fun i => A ((arithmeticChild P .central).frame.perm i)
theorem incomingRole_proper (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    Proper (incomingRole P A) := by
  obtain ⟨j, hj⟩ := hA
  refine ⟨(arithmeticChild P .central).frame.inverse j, ?_⟩
  simpa [incomingRole, (arithmeticChild P .central).frame.right_inverse] using hj
noncomputable def incomingPose (P : Parameters) (A : Mask P.p) (hA : Proper A) : Pose P.p :=
  (arithmeticChild P .central).relative
    (arithmeticChild P (.outer (incomingRole P A) (incomingRole_proper P A hA)))
@[simp] theorem incoming_negative (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (i : Fin P.p) : (incomingPose P A hA).frame.negative i = A i := by
  unfold incomingPose
  rw [relative_negative, child_central_negative, child_outer_negative]
  simp [incomingRole, (arithmeticChild P .central).frame.right_inverse]
@[simp] theorem incoming_anchor (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (i : Fin P.p) : (incomingPose P A hA).anchor i = 4 * bit (A i) - 1 := by
  unfold incomingPose
  rw [relative_anchor, child_outer_anchor, child_central_anchor]
  simp [RegisteredFrame.sign, incomingRole, (arithmeticChild P .central).frame.right_inverse, bit]
  cases A i <;> rfl
theorem incoming_support (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    IncomingSupport (incomingPose P A hA) A := by
  constructor
  · funext i
    simp only [boxLower, incoming_anchor, incoming_negative]
    omega
  · funext i
    rw [hole_coordinate, incoming_anchor, incoming_negative]
    omega
theorem central_outer_face_contact (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    FaceContact (arithmeticChild P .central) (arithmeticChild P (.outer A hA)) := by
  obtain ⟨j, hj⟩ := hA
  let c : Cell P.p := fun i => 1 + bit (A i)
  let d : Cell P.p := fun i => c i - if i = j then 1 else 0
  have hc : CentralCell c := central_fills_outer_hole A ⟨j, hj⟩
  have hd : OuterCell A d := by
    constructor
    · intro i
      by_cases hi : i = j
      · subst i
        simp [d, c, bit, hj]
      · cases ha : A i <;> simp [d, c, bit, ha, hi]
    · intro hh
      have h := hh j
      simp [d, c, bit, hj] at h
  constructor
  · intro x ⟨hcx, hdx⟩
    exact outer_central_disjoint ((outer_image_iff P A ⟨j, hj⟩ x).mp hdx)
      ((central_image_iff P x).mp hcx)
  · refine ⟨c, d, (central_image_iff P c).mpr hc,
      (outer_image_iff P A ⟨j, hj⟩ d).mpr hd, j, ?_, ?_⟩
    · left
      simp [d]
    · intro i hi
      simp [d, hi]
theorem identity_refine_same (P : Parameters) (a : Role P.p) :
    (refine P (identityPose P.p) a).Same (arithmeticChild P a) := by
  constructor
  · intro i
    rfl
  constructor
  · intro i
    simp [refine, Pose.comp, RegisteredFrame.comp, identityPose]
  · intro i
    simp [refine, Pose.comp, RegisteredFrame.linear, RegisteredFrame.sign, identityPose]
theorem child_is_descendant (P : Parameters) (a : Role P.p) :
    Descendant P 1 (identityPose P.p) (arithmeticChild P a) :=
  ⟨a, identity_refine_same P a⟩
theorem incoming_generated (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    GeneratedContact P (incomingPose P A hA) := by
  let B := incomingRole P A
  have hB := incomingRole_proper P A hA
  refine ⟨1, arithmeticChild P .central, arithmeticChild P (.outer B hB),
    child_is_descendant P .central, child_is_descendant P (.outer B hB),
    central_outer_face_contact P B hB, ?_⟩
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
theorem IncomingSupport.role_unique {p : Nat} {q : Pose p} {A B : Mask p}
    (ha : IncomingSupport q A) (hb : IncomingSupport q B) : A = B := by
  funext i
  have h := congrFun (ha.2.symm.trans hb.2) i
  cases hA : A i <;> cases hB : B i <;> simp [bit, hA, hB] at h ⊢
def IncomingFrameProperty (P : Parameters) : Prop :=
  ∀ q, GeneratedContact P q → ∀ A (hA : Proper A), IncomingSupport q A →
    q.Same (incomingPose P A hA)
theorem registered_marked_fan_of_incoming_frames (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (hroot : W.tiles (identityPose P.p)) (hframes : IncomingFrameProperty P)
    {A : Mask P.p} (hA : Proper A) (hnA : NonemptyMask A)
    (hin : (normalizedLocalPatch P W hl hroot (generated_wall_property P)).incoming A) :
    ∀ B (hB : Proper B), ∃ q, W.tiles q ∧ q.Same (incomingPose P B hB) := by
  intro B hB
  obtain ⟨q, hq, hs⟩ := registered_support_fan_unconditional P W hl hroot hA hnA hin B hB
  exact ⟨q, hq.1, hframes q (generated_of_root_neighbor P W hl hroot q hq.1 hq.2) B hB hs⟩
end RegisteredPrime
