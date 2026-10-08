module
public import RegisteredPrime.ScalarEquivariance
@[expose] public section
namespace RegisteredPrime

def H0Pose (p : Nat) : Pose p where
  frame := (identityPose p).frame
  anchor := fun _ => 1

theorem empty_proper (P : Parameters) : Proper (fun _ : Fin P.p => false) :=
  ⟨⟨0, by have := P.prime.two_le; omega⟩, rfl⟩

noncomputable def outgoingSeed (P : Parameters) (A : Mask P.p) (hA : Proper A) : Pose P.p :=
  (arithmeticChild P (.outer A hA)).relative (arithmeticChild P .central)

def OutgoingSeed (P : Parameters) (e : Pose P.p) : Prop :=
  ∃ A, ∃ hA : Proper A, e = outgoingSeed P A hA

theorem empty_child_frame (P : Parameters) :
    (arithmeticChild P (.outer (fun _ => false) (empty_proper P))).frame =
      (arithmeticChild P .central).frame := by
  apply RegisteredFrame.ext_data
  · funext i
    apply Fin.ext
    simp [arithmeticChild, childIndex, childFrame, empty_outer_frame]
  · funext i
    rw [child_outer_negative, child_central_negative]

theorem empty_outgoing_is_H0 (P : Parameters) :
    outgoingSeed P (fun _ => false) (empty_proper P) = H0Pose P.p := by
  apply Pose.Same.eq
  constructor
  · intro i
    change (arithmeticChild P .central).frame.perm
      ((arithmeticChild P (.outer (fun _ => false) (empty_proper P))).frame.inverse i) = i
    rw [empty_child_frame]
    exact (arithmeticChild P .central).frame.right_inverse i
  constructor
  · intro i
    change (outgoingSeed P (fun _ => false) (empty_proper P)).frame.negative i = false
    unfold outgoingSeed
    rw [relative_negative, child_outer_negative, child_central_negative]
    rfl
  · intro i
    change (outgoingSeed P (fun _ => false) (empty_proper P)).anchor i = 1
    unfold outgoingSeed
    rw [relative_anchor, child_outer_anchor, child_central_anchor]
    simp [RegisteredFrame.sign]

theorem H0_is_seed (P : Parameters) : OutgoingSeed P (H0Pose P.p) :=
  ⟨fun _ => false, empty_proper P, (empty_outgoing_is_H0 P).symm⟩

theorem H0_owns_one (P : Parameters) : Occupies (H0Pose P.p) (fun _ => 1) := by
  refine ⟨fun _ => 0, ⟨fun _ => Or.inl rfl,
    ⟨⟨0, by have := P.prime.two_le; omega⟩, rfl⟩⟩, ?_⟩
  funext i
  simp [Pose.cell, H0Pose, identityPose, RegisteredFrame.linear, RegisteredFrame.sign, bit]

theorem posed_H0_owns_hole (P : Parameters) (q : Pose P.p) :
    Occupies (q.comp (H0Pose P.p)) (hole q) := by
  rw [occupies_comp_iff]
  have he : q.inv.cell (hole q) = (fun _ => (1 : Int)) := q.inv_cell_cell _
  rw [he]
  exact H0_owns_one P

theorem Pose.relative_comp {p : Nat} (q r : Pose p) : q.relative (q.comp r) = r := by
  unfold Pose.relative
  rw [← Pose.comp_assoc, Pose.inv_comp, Pose.identity_comp]

/-- The exact full-pose commuting square for a sibling hole, including A=empty.
This upgrades the earlier modular index carry to an equality of marked poses. -/
theorem sibling_hole_carry_square (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    refine P (arithmeticChild P .central)
      (.outer (scalarRole P A) (scalarRole_proper P A hA)) =
      (refine P (arithmeticChild P (.outer A hA)) .central).comp (H0Pose P.p) := by
  apply Pose.Same.eq
  constructor
  · intro i
    change (arithmeticChild P (.outer (scalarRole P A) (scalarRole_proper P A hA))).frame.perm
        ((arithmeticChild P .central).frame.perm i) =
      (arithmeticChild P .central).frame.perm ((arithmeticChild P (.outer A hA)).frame.perm i)
    exact child_scalar_permutation P A hA i
  constructor
  · intro i
    simp [refine, Pose.comp, RegisteredFrame.comp, H0Pose, identityPose]
  · intro i
    change (refine P (arithmeticChild P .central)
      (.outer (scalarRole P A) (scalarRole_proper P A hA))).anchor i =
      (refine P (arithmeticChild P (.outer A hA)) .central).anchor i +
      (refine P (arithmeticChild P (.outer A hA)) .central).frame.sign i * 1
    rw [refine_outer_anchor, refine_central_anchor]
    simp only [child_central_anchor, child_outer_anchor, RegisteredFrame.sign,
      child_central_negative, refine_central_negative, child_outer_negative,
      scalarRole_at]
    cases h : A i <;> simp [h] <;> omega

/-- A coarse outgoing sibling normal produces an actual fine H0 owner, in any
common full parent frame. No catalog exhaustion is assumed here. -/
theorem seed_carry_owner (P : Parameters) (q r : Pose P.p) (A : Mask P.p) (hA : Proper A)
    (hseed : q.relative r = outgoingSeed P A hA) :
    refine P r (.outer (scalarRole P A) (scalarRole_proper P A hA)) =
      (refine P q .central).comp (H0Pose P.p) := by
  let Q := arithmeticChild P (.outer A hA)
  let C := arithmeticChild P .central
  let t := q.comp Q.inv
  have hq : t.comp Q = q := by
    dsimp [t]
    rw [Pose.comp_assoc, Pose.inv_comp, Pose.comp_identity]
  have hr : t.comp C = r := by
    dsimp [t]
    rw [Pose.comp_assoc]
    change q.comp (outgoingSeed P A hA) = r
    rw [← hseed, Pose.comp_relative]
  have hq' : refine P q .central = (doubleAnchor t).comp (refine P Q .central) := by
    rw [← hq, refine_comp]
  have hr' : refine P r (.outer (scalarRole P A) (scalarRole_proper P A hA)) =
      (doubleAnchor t).comp (refine P C (.outer (scalarRole P A) (scalarRole_proper P A hA))) := by
    rw [← hr, refine_comp]
  rw [hr', hq']
  change (doubleAnchor t).comp
      (refine P (arithmeticChild P .central) (.outer (scalarRole P A) (scalarRole_proper P A hA))) = _
  rw [sibling_hole_carry_square, Pose.comp_assoc]

end RegisteredPrime
