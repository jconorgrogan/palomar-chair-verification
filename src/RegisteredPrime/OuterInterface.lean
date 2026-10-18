module
public import RegisteredPrime.ContactProjection
@[expose] public section
namespace RegisteredPrime

theorem Adjacent.symm {p : Nat} {a b : Cell p} (h : Adjacent a b) : Adjacent b a := by
  obtain ⟨j, hj, ht⟩ := h
  exact ⟨j, hj.symm, fun i hi => (ht i hi).symm⟩

theorem FaceContact.symm {p : Nat} {q r : Pose p} (h : FaceContact q r) : FaceContact r q := by
  obtain ⟨hd, a, b, ha, hb, hab⟩ := h
  exact ⟨fun c hc => hd c hc.symm, b, a, hb, ha, hab.symm⟩

/-- Two adjacent side-two boxes with one omitted cell apiece still share an
actual unit face when p≥3. Two distinct transverse coordinates avoid the holes. -/
theorem positive_boxes_face_contact {p : Nat} (hp : 3 ≤ p) (q r : Pose p)
    (j : Fin p) (hj : boxLower r j = boxLower q j + 2)
    (ht : ∀ i, i ≠ j → boxLower q i = boxLower r i) : FaceContact q r := by
  obtain ⟨k, hkj, _⟩ := third_axis hp j j
  obtain ⟨l, hlj, hlk⟩ := third_axis hp j k
  let a : Cell p := fun i => boxLower q i + if i = j then 1 else
    if i = k then bit (q.frame.negative k) else if i = l then bit (r.frame.negative l) else 0
  let b : Cell p := fun i => a i + if i = j then 1 else 0
  have habox : ∀ i, a i = boxLower q i ∨ a i = boxLower q i + 1 := by
    intro i
    by_cases hij : i = j
    · simp [a, hij]
    · by_cases hik : i = k
      · subst i
        cases hn : q.frame.negative k <;> simp [a, hkj, bit, hn]
      · by_cases hil : i = l
        · subst i
          cases hn : r.frame.negative l <;> simp [a, hlj, hlk, bit, hn]
        · simp [a, hij, hik, hil]
  have hbbox : ∀ i, b i = boxLower r i ∨ b i = boxLower r i + 1 := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [a, b, hj]
      omega
    · have h := habox i
      simp only [b, ite_eq_right hij, Int.add_zero]
      rwa [ht i hij] at h
  have hqa : Occupies q a := by
    apply (occupies_box_iff q a).mpr
    refine ⟨habox, ?_⟩
    intro he
    have hk := congrFun he k
    rw [hole_from_box] at hk
    cases hn : q.frame.negative k <;> simp [a, hkj, bit, hn] at hk <;> omega
  have hrb : Occupies r b := by
    apply (occupies_box_iff r b).mpr
    refine ⟨hbbox, ?_⟩
    intro he
    have hl := congrFun he l
    rw [hole_from_box] at hl
    have hbox := ht l hlj
    cases hn : r.frame.negative l <;> simp [a, b, hlj, hlk, bit, hn] at hl <;> omega
  refine ⟨?_, a, b, hqa, hrb, j, Or.inr ?_, ?_⟩
  · intro c ⟨hqc, hrc⟩
    have hqj := ((occupies_box_iff q c).mp hqc).1 j
    have hrj := ((occupies_box_iff r c).mp hrc).1 j
    omega
  · simp [b]
  · intro i hij
    simp [b, hij]

theorem box_adjacent_face_contact {p : Nat} (hp : 3 ≤ p) (q r : Pose p)
    (h : BoxAdjacent q r) : FaceContact q r := by
  obtain ⟨j, hj, ht⟩ := h
  rcases hj with hj | hj
  · exact positive_boxes_face_contact hp q r j hj ht
  · exact (positive_boxes_face_contact hp r q j hj (fun i hi => (ht i hi).symm)).symm

/-- Each macrocell face shared by two coarse chairs has an actual outer/outer
fine contact. This explicitly discharges the missing-panel existence issue. -/
theorem refined_outer_contact_of_adjacent_cells (P : Parameters) (q r : Pose P.p)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B)
    (hc : Adjacent (q.cell (fun i => bit (A i))) (r.cell (fun i => bit (B i)))) :
    FaceContact (refine P q (.outer A hA)) (refine P r (.outer B hB)) := by
  apply box_adjacent_face_contact (P.prime.three_le P.odd)
  obtain ⟨j, hj, ht⟩ := hc
  refine ⟨j, ?_, ?_⟩
  · rw [refine_outer_macrocell, refine_outer_macrocell]
    omega
  · intro i hij
    rw [refine_outer_macrocell, refine_outer_macrocell, ht i hij]

end RegisteredPrime
