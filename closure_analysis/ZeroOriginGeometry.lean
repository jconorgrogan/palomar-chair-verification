module
public import RegisteredPrime.ContactProjection
@[expose] public section
namespace RegisteredPrime

/-- Zero relative anchor is exactly equality of the two anchors. -/
theorem relative_anchor_zero_iff {p : Nat} (q r : Pose p) :
    (∀ i, (q.relative r).anchor i = 0) ↔ q.anchor = r.anchor := by
  constructor
  · intro h
    funext i
    have hi := h (q.frame.perm i)
    rw [relative_anchor, q.frame.left_inverse] at hi
    cases hn : q.frame.negative i <;> simp [RegisteredFrame.sign, hn] at hi <;> omega
  · intro h i
    rw [relative_anchor, h]
    simp

/-- Equality of anchors commutes with normalization of two refined parents. -/
theorem refined_same_anchor_normalized (P : Parameters) (q r : Pose P.p)
    (a b : Role P.p) (h : (refine P q a).anchor = (refine P r b).anchor) :
    (arithmeticChild P a).anchor = (refine P (q.relative r) b).anchor := by
  apply (relative_anchor_zero_iff _ _).mp
  intro i
  have hi := (relative_anchor_zero_iff (refine P q a) (refine P r b)).mpr h i
  rw [refine_relative] at hi
  exact hi

/-- Equal fine anchors cannot mix the central and outer parity classes. -/
theorem refined_same_anchor_centralBit (P : Parameters) (q r : Pose P.p)
    (a b : Role P.p) (h : (refine P q a).anchor = (refine P r b).anchor) :
    centralBit a = centralBit b := by
  let i : Fin P.p := ⟨0, by have := P.prime.two_le; omega⟩
  have hq := refine_anchor_parity P q a i
  have hr := refine_anchor_parity P r b i
  rw [h] at hq
  cases ha : centralBit a <;> cases hb : centralBit b <;>
    simp [ha, hb, bit] at hq hr ⊢ <;> omega

/-- A central child of a uniformly registered parent has the central carrier color. -/
theorem refine_central_colored (P : Parameters) (q : Pose P.p)
    (hq : q.UniformParity) : CentralColored (refine P q .central) := by
  obtain ⟨b, hb⟩ := hq
  have hbox := uniform_parity_box q b hb
  constructor
  · intro i
    rw [refine_central_lower]
    omega
  · refine ⟨b, fun i => ?_⟩
    rw [refine_central_lower]
    have he : (2 * boxLower q i + 1) / 2 = boxLower q i := by omega
    rw [he]
    exact hbox i

/-- Two central children never have a face contact. This uses only the
parent parity invariant and the already proved carrier-color geometry. -/
theorem refined_central_not_contact (P : Parameters) (q r : Pose P.p)
    (hq : q.UniformParity) (hr : r.UniformParity) :
    ¬ FaceContact (refine P q .central) (refine P r .central) := by
  intro hc
  have hp := P.prime.three_le P.odd
  have hqc := refine_central_colored P q hq
  have hrc := refine_central_colored P r hr
  have ha := contact_box_adjacent hp _ _ hc (fun i => (hqc.1 i).trans (hrc.1 i).symm)
  exact central_colored_not_adjacent hp _ _ hqc hrc ha

/-- Refinement of one parent has distinct anchors for its distinct roles,
including the separately stipulated empty role. -/
theorem refine_anchor_injective (P : Parameters) (q : Pose P.p)
    (a b : Role P.p) (h : (refine P q a).anchor = (refine P q b).anchor) : a = b := by
  have hbit := refined_same_anchor_centralBit P q q a b h
  cases a with
  | central =>
    cases b with
    | central => rfl
    | outer B hB => simp [centralBit] at hbit
  | outer A hA =>
    cases b with
    | central => simp [centralBit] at hbit
    | outer B hB =>
      have he : A = B := by
        funext i
        have hi := congrFun h (q.frame.inverse i)
        rw [refine_outer_anchor, refine_outer_anchor, q.frame.right_inverse] at hi
        cases hn : q.frame.negative (q.frame.inverse i) <;>
          cases ha : A i <;> cases hb : B i <;>
          simp [RegisteredFrame.sign, hn, ha, hb] at hi ⊢ <;> omega
      cases he
      rfl

/-- Equal-anchor contacting fine tiles have distinct actual parents, and
therefore their fine face edge projects to a genuine parent face edge. -/
theorem finite_equal_anchor_contact_parents (P : Parameters) (n : Nat)
    (root q r : Pose P.p) (hq : Descendant P n root q) (hr : Descendant P n root r)
    (a b : Role P.p) (hc : FaceContact (refine P q a) (refine P r b))
    (h : (refine P q a).anchor = (refine P r b).anchor) : FaceContact q r := by
  rcases finite_refined_contact_parents P n root q r hq hr a b hc with he | he
  · subst r
    have hab := refine_anchor_injective P q a b h
    subst b
    obtain ⟨hd, x, y, hx, _, _⟩ := hc
    exact False.elim (hd x ⟨hx, hx⟩)
  · exact he

/-- All equal-anchor contacts between generated fine tiles use outer roles. -/
theorem generated_equal_anchor_contact_outer (P : Parameters) (n : Nat)
    (q r : Pose P.p) (hq : Descendant P n (identityPose P.p) q)
    (hr : Descendant P n (identityPose P.p) r) (a b : Role P.p)
    (hc : FaceContact (refine P q a) (refine P r b))
    (h : (refine P q a).anchor = (refine P r b).anchor) :
    ∃ A hA B hB, a = Role.outer A hA ∧ b = Role.outer B hB := by
  have hbit := refined_same_anchor_centralBit P q r a b h
  cases a with
  | central =>
    cases b with
    | outer B hB => simp [centralBit] at hbit
    | central =>
      have hu : (identityPose P.p).UniformParity := ⟨false, fun _ => rfl⟩
      exact False.elim (refined_central_not_contact P q r
        (descendant_uniform_parity P n _ _ hu hq)
        (descendant_uniform_parity P n _ _ hu hr) hc)
  | outer A hA =>
    cases b with
    | central => simp [centralBit] at hbit
    | outer B hB => exact ⟨A, hA, B, hB, rfl, rfl⟩

/-- The normalized coordinate equation for equal-anchor outer children. -/
theorem outer_same_anchor_equation (P : Parameters) (q r : Pose P.p)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B)
    (h : (refine P q (.outer A hA)).anchor = (refine P r (.outer B hB)).anchor) :
    ∀ i, (if A i then (4 : Int) else 0) =
      2 * (q.relative r).anchor i + (q.relative r).frame.sign i *
        (if B ((q.relative r).frame.perm i) then 4 else 0) := by
  have he := refined_same_anchor_normalized P q r (.outer A hA) (.outer B hB) h
  intro i
  exact congrFun he i

/-- Equal-anchor outer children force even parent-relative translation. -/
theorem outer_same_anchor_parent_even (P : Parameters) (q r : Pose P.p)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B)
    (h : (refine P q (.outer A hA)).anchor = (refine P r (.outer B hB)).anchor) :
    ∀ i, (q.relative r).anchor i % 2 = 0 := by
  intro i
  have hi := outer_same_anchor_equation P q r A B hA hB h i
  cases hn : (q.relative r).frame.negative i <;>
    cases ha : A i <;> cases hb : B ((q.relative r).frame.perm i) <;>
    simp [RegisteredFrame.sign, ha, hb] at hi <;> omega

/-- Read the singleton/complement sign mask from the checked geometric wall
condition. Color false is singleton; color true is complement. -/
theorem wall_geometry_sign_mask {p : Nat} (e : Pose p) (hw : WallGeometry e) :
    ∃ j side color, boxLower e = wallBox j side ∧
      ∀ i, e.frame.negative i = if i = j then !color else color := by
  obtain ⟨j, hw | hw⟩ := hw
  · obtain ⟨hb, hh | hh⟩ := hw
    · refine ⟨j, true, false, hb, fun i => ?_⟩
      have hi := congrFun hh i
      rw [hole_from_box, congrFun hb i] at hi
      cases hn : e.frame.negative i <;> by_cases hij : i = j <;>
        simp_all [wallBox, unitAxis, bit] <;> omega
    · refine ⟨j, true, true, hb, fun i => ?_⟩
      have hi := congrFun hh i
      rw [hole_from_box, congrFun hb i] at hi
      cases hn : e.frame.negative i <;> by_cases hij : i = j <;>
        simp_all [wallBox, unitAxis, bit] <;> omega
  · obtain ⟨hb, hh | hh⟩ := hw
    · refine ⟨j, false, false, hb, fun i => ?_⟩
      have hi := congrFun hh i
      rw [hole_from_box, congrFun hb i] at hi
      cases hn : e.frame.negative i <;> by_cases hij : i = j <;>
        simp_all [wallBox, unitAxis, bit] <;> omega
    · refine ⟨j, false, true, hb, fun i => ?_⟩
      have hi := congrFun hh i
      rw [hole_from_box, congrFun hb i] at hi
      cases hn : e.frame.negative i <;> by_cases hij : i = j <;>
        simp_all [wallBox, unitAxis, bit] <;> omega

/-- An even parent wall and equal child anchors leave just equal or
complementary pulled-back outer roles. In the equal-role case, an empty
root role forces zero parent anchor, the induction's unique exceptional case. -/
theorem wall_equal_anchor_outer_roles {p : Nat} (e : Pose p) (A B : Mask p)
    (hw : WallGeometry e)
    (he : ∀ i, (if A i then (4 : Int) else 0) =
      2 * e.anchor i + e.frame.sign i * (if B (e.frame.perm i) then 4 else 0)) :
    ((∀ i, B (e.frame.perm i) = A i) ∧
      (A = (fun _ => false) → ∀ i, e.anchor i = 0)) ∨
    (∀ i, B (e.frame.perm i) = !(A i)) := by
  obtain ⟨j, side, color, hb, hm⟩ := wall_geometry_sign_mask e hw
  cases color with
  | false =>
    have hroles : ∀ i, B (e.frame.perm i) = A i := by
      intro i
      have hi := he i
      have hbi := congrFun hb i
      simp only [RegisteredFrame.sign] at hi
      simp only [boxLower] at hbi
      rw [hm i] at hi hbi
      cases side <;> by_cases hij : i = j <;>
        cases ha : A i <;> cases hc : B (e.frame.perm i) <;>
        (try simp only [hij] at ha hc) <;>
        simp [wallBox, bit, hij, ha, hc] at hi hbi ⊢ <;> omega
    exact Or.inl ⟨hroles, fun ha i => by
      have hi := he i
      rw [hroles i, ha] at hi
      simp at hi
      omega⟩
  | true =>
    right
    intro i
    have hi := he i
    have hbi := congrFun hb i
    simp only [RegisteredFrame.sign] at hi
    simp only [boxLower] at hbi
    rw [hm i] at hi hbi
    cases side <;> by_cases hij : i = j <;>
      cases ha : A i <;> cases hc : B (e.frame.perm i) <;>
      (try simp only [hij] at ha hc) <;>
        simp [wallBox, bit, hij, ha, hc] at hi hbi ⊢ <;> omega


/-- Ready-to-use geometric reduction for the generated zero-origin induction.
Every hypothesis refers to actual descendants and actual face contact. -/
theorem generated_equal_anchor_contact_parent_data (P : Parameters) (n : Nat)
    (q r : Pose P.p) (hq : Descendant P n (identityPose P.p) q)
    (hr : Descendant P n (identityPose P.p) r) (a b : Role P.p)
    (hc : FaceContact (refine P q a) (refine P r b))
    (h : (refine P q a).anchor = (refine P r b).anchor) :
    ∃ A hA B hB, a = Role.outer A hA ∧ b = Role.outer B hB ∧
      GeneratedContact P (q.relative r) ∧ WallGeometry (q.relative r) ∧
      (((∀ i, B ((q.relative r).frame.perm i) = A i) ∧
        (A = (fun _ => false) → ∀ i, (q.relative r).anchor i = 0)) ∨
        (∀ i, B ((q.relative r).frame.perm i) = !(A i))) := by
  obtain ⟨A, hA, B, hB, rfl, rfl⟩ :=
    generated_equal_anchor_contact_outer P n q r hq hr a b hc h
  have hp := finite_equal_anchor_contact_parents P n (identityPose P.p)
    q r hq hr (.outer A hA) (.outer B hB) hc h
  have he : GeneratedContact P (q.relative r) :=
    ⟨n, q, r, hq, hr, hp, Pose.Same.refl _⟩
  have hw := generated_wall_property P (q.relative r) he
    (outer_same_anchor_parent_even P q r A B hA hB h)
  exact ⟨A, hA, B, hB, rfl, rfl, he, hw,
    wall_equal_anchor_outer_roles _ A B hw (outer_same_anchor_equation P q r A B hA hB h)⟩

end RegisteredPrime
