module
public import WeakRecognition.CoarseWorld
@[expose] public section
namespace RegisteredPrime

/-- An outgoing arithmetic sibling normal with no negative coordinate is
exactly H0. This does not classify any wall contact. -/
theorem outgoing_seed_empty_negative (P : Parameters) (e : Pose P.p)
    (hs : OutgoingSeed P e) (hn : ∀ i, e.frame.negative i = false) : e = H0Pose P.p := by
  obtain ⟨A, hA, rfl⟩ := hs
  have hA0 : A = fun _ => false := by
    funext i
    have hi := hn ((arithmeticChild P (.outer A hA)).frame.perm i)
    unfold outgoingSeed at hi
    rw [relative_negative, (arithmeticChild P (.outer A hA)).frame.left_inverse,
      child_outer_negative, child_central_negative] at hi
    simpa using hi
  subst A
  exact empty_outgoing_is_H0 P

/-- One fixed refined role determines its entire registered parent pose. -/
theorem refine_fixed_role_injective (P : Parameters) (q r : Pose P.p) (a : Role P.p)
    (h : refine P q a = refine P r a) : q = r := by
  have he := congrArg (fun t => t.comp (arithmeticChild P a).inv) h
  change ((doubleAnchor q).comp (arithmeticChild P a)).comp (arithmeticChild P a).inv =
    ((doubleAnchor r).comp (arithmeticChild P a)).comp (arithmeticChild P a).inv at he
  simp only [Pose.comp_assoc, Pose.comp_inv, Pose.comp_identity] at he
  exact doubleAnchor_injective q r he

/-- The occupied lower corner of a chair has a unique proper local Boolean
role; at that corner its pulled-back bits are the frame's negative mask. -/
theorem lower_corner_owner_role (P : Parameters) (e : Pose P.p)
    (hb : boxLower e = (fun _ => 1)) (ho : Occupies e (fun _ => 1)) :
    ∃ B, ∃ _hB : Proper B, e.cell (fun i => bit (B i)) = (fun _ => 1) ∧
      ∀ i, B (e.frame.perm i) = e.frame.negative i := by
  classical
  obtain ⟨b, hbu, heb⟩ := ho
  let B : Mask P.p := fun i => decide (b i = 1)
  have hbits : (fun i => bit (B i)) = b := by
    funext i
    rcases hbu.1 i with hi | hi <;> simp [B, bit, hi]
  have hB : Proper B := by
    obtain ⟨j, hj⟩ := hbu.2
    exact ⟨j, by simp [B, hj]⟩
  have hcell : e.cell (fun i => bit (B i)) = (fun _ => 1) := by rw [hbits]; exact heb
  refine ⟨B, hB, hcell, fun i => ?_⟩
  have hc := congrFun hcell i
  have hbi := congrFun hb i
  cases hn : e.frame.negative i <;> cases hBf : B (e.frame.perm i) <;>
    simp [Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, boxLower,
      bit, hn, hBf] at hc hbi ⊢ <;> omega

/-- The outer child above the coarse lower corner has positive signs and
anchor 2 in every coordinate, before any arithmetic frame restriction. -/
theorem refine_lower_corner_geometry (P : Parameters) (e : Pose P.p)
    (hb : boxLower e = (fun _ => 1)) (B : Mask P.p) (hB : Proper B)
    (hmask : ∀ i, B (e.frame.perm i) = e.frame.negative i) :
    (∀ i, (refine P e (.outer B hB)).frame.negative i = false) ∧
      (∀ i, (refine P e (.outer B hB)).anchor i = 2) := by
  constructor
  · intro i
    rw [refine_outer_negative, hmask i]
    simp
  · intro i
    have hbi := congrFun hb i
    rw [refine_outer_anchor, hmask i]
    cases hn : e.frame.negative i <;>
      simp [boxLower, RegisteredFrame.sign, bit, hn] at hbi ⊢ <;> omega

/-- Coarse disjointness makes every pair of refined children disjoint. -/
theorem disjoint_refined_children (P : Parameters) (q r : Pose P.p)
    (hd : Disjoint q r) (a b : Role P.p) : Disjoint (refine P q a) (refine P r b) := by
  intro c ⟨hq, hr⟩
  exact hd (floorCell c) ⟨refine_occupies_parent P q a c hq,
    refine_occupies_parent P r b c hr⟩

/-- Local exact-pose coarse-hole preservation. The assumptions are explicit
coarse geometry and recognition of actual cross-child contacts, not E-legality
or a hierarchy/recognizability assumption on the coarse parents. -/
theorem coarse_outgoing_seed_of_child_recognition (P : Parameters) (e : Pose P.p)
    (hb : boxLower e = (fun _ => 1)) (ho : Occupies e (fun _ => 1))
    (hd : Disjoint (identityPose P.p) e)
    (hl : WeakRecognition.ChildRecognition P (identityPose P.p) (doubleAnchor e)) :
    OutgoingSeed P e := by
  obtain ⟨B, hB, _, hmask⟩ := lower_corner_owner_role P e hb ho
  have hgeom := refine_lower_corner_geometry P e hb B hB hmask
  let C := arithmeticChild P .central
  let R := refine P e (.outer B hB)
  have hown : Occupies R (hole C) := by
    refine ⟨fun _ => 0, ⟨fun _ => Or.inl rfl,
      ⟨⟨0, by have := P.prime.two_le; omega⟩, rfl⟩⟩, ?_⟩
    funext i
    change R.anchor i + R.frame.sign i * (0 : Int) - bit (R.frame.negative i) = hole C i
    have hn := hgeom.1 i
    have ha := hgeom.2 i
    change R.frame.negative i = false at hn
    change R.anchor i = 2 at ha
    rw [ha, hn, hole_coordinate]
    simp [C, bit, child_central_anchor, child_central_negative]
  have hdis : Disjoint C R := by
    have hh := disjoint_refined_children P (identityPose P.p) e hd .central (.outer B hB)
    rw [(identity_refine_same P .central).eq] at hh
    exact hh
  have hc := hole_owner_face_contact (P.prime.three_le P.odd) C R hdis hown
  have hrec : RecognitionContact P (C.relative R) := by
    have hcontact : FaceContact ((identityPose P.p).comp (arithmeticChild P .central))
        ((doubleAnchor e).comp (arithmeticChild P (.outer B hB))) := by
      simpa only [Pose.identity_comp, C, R, refine, doubleAnchor] using hc
    have hh := hl .central (.outer B hB) hcontact
    simpa only [Pose.identity_comp, C, R, refine, doubleAnchor] using hh
  have hrelown : Occupies (C.relative R) (fun _ => 1) := by
    have hh : Occupies (C.comp (C.relative R)) (hole C) := by
      rw [Pose.comp_relative]
      exact hown
    rw [occupies_comp_iff] at hh
    have he : C.inv.cell (hole C) = (fun _ => (1 : Int)) := C.inv_cell_cell _
    rwa [he] at hh
  have hrelneg : ∀ i, (C.relative R).frame.negative i = false := by
    intro i
    rw [relative_negative]
    have hnr := hgeom.1 (C.frame.inverse i)
    change R.frame.negative (C.frame.inverse i) = false at hnr
    rw [hnr]
    change xor ((arithmeticChild P .central).frame.negative (C.frame.inverse i)) false = false
    rw [child_central_negative]
    rfl
  have hH0 := outgoing_seed_empty_negative P (C.relative R) (hrec.outgoing hrelown) hrelneg
  have hR : R = C.comp (H0Pose P.p) := by
    have hh := congrArg (fun t => C.comp t) hH0
    rwa [Pose.comp_relative] at hh
  let A := incomingRole P B
  have hA : Proper A := incomingRole_proper P B hB
  have hscalar : scalarRole P A = B := by
    funext i
    simp [A, scalarRole, incomingRole, (arithmeticChild P .central).frame.right_inverse]
  let S := outgoingSeed P A hA
  have hseed : (identityPose P.p).relative S = outgoingSeed P A hA :=
    (relative_identity_same S).eq
  have hcarry := seed_carry_owner P (identityPose P.p) S A hA hseed
  have hS : refine P S (.outer B hB) = C.comp (H0Pose P.p) := by
    simpa only [hscalar, (identity_refine_same P .central).eq] using hcarry
  refine ⟨A, hA, ?_⟩
  exact refine_fixed_role_injective P e S (.outer B hB) (hR.trans hS.symm)

end RegisteredPrime
