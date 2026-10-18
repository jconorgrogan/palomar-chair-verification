module
public import RegisteredPrime.ContactBoxAlignment
@[expose] public section
namespace RegisteredPrime
theorem outer_colored_mask {p : Nat} (q r : Pose p) (hq : OuterColored q)
    (hr : OuterColored r) (j : Fin p)
    (haxis : boxLower r j = boxLower q j + 2 ∨ boxLower q j = boxLower r j + 2)
    (htrans : ∀ i, i ≠ j → boxLower q i = boxLower r i) :
    ∃ b : Bool, ∀ i, xor (q.frame.negative i) (r.frame.negative i) =
      if i = j then !b else b := by
  obtain ⟨hqe, b, hb⟩ := hq
  obtain ⟨hre, c, hc⟩ := hr
  refine ⟨xor b c, fun i => ?_⟩
  have h1 := hb i
  have h2 := hc i
  by_cases hij : i = j
  · subst i
    have he := hqe j
    have hd : boxLower r j / 2 = boxLower q j / 2 + 1 ∨
        boxLower q j / 2 = boxLower r j / 2 + 1 := by omega
    cases b <;> cases c <;> cases hn : q.frame.negative j <;>
      cases hm : r.frame.negative j <;> simp [bit, hn, hm] at h1 h2 ⊢ <;> omega
  · have he := htrans i hij
    rw [he] at h1
    cases b <;> cases c <;> cases hn : q.frame.negative i <;>
      cases hm : r.frame.negative i <;> simp [bit, hn, hm, hij] at h1 h2 ⊢ <;> omega
theorem central_colored_not_adjacent {p : Nat} (hp : 3 ≤ p) (q r : Pose p)
    (hq : CentralColored q) (hr : CentralColored r) (ha : BoxAdjacent q r) : False := by
  obtain ⟨hqo, b, hb⟩ := hq
  obtain ⟨hro, c, hc⟩ := hr
  obtain ⟨j, haxis, htrans⟩ := ha
  obtain ⟨k, hkj, _⟩ := third_axis hp j j
  have h1 := hb k
  have h2 := hc k
  have he := htrans k hkj
  rw [he] at h1
  have h3 := hb j
  have h4 := hc j
  have hodd := hqo j
  have hd : boxLower r j / 2 = boxLower q j / 2 + 1 ∨
      boxLower q j / 2 = boxLower r j / 2 + 1 := by omega
  cases b <;> cases c <;> simp [bit] at h1 h2 h3 h4 <;> omega
theorem colored_contact_mask {p : Nat} (hp : 3 ≤ p) (q r : Pose p)
    (hq : CarrierColored q) (hr : CarrierColored r) (hc : FaceContact q r)
    (hpar : ∀ i, boxLower q i % 2 = boxLower r i % 2) :
    ∃ j, (boxLower r j = boxLower q j + 2 ∨ boxLower q j = boxLower r j + 2) ∧
      (∀ i, i ≠ j → boxLower q i = boxLower r i) ∧
      ∃ b : Bool, ∀ i, xor (q.frame.negative i) (r.frame.negative i) =
        if i = j then !b else b := by
  have ha := contact_box_adjacent hp q r hc hpar
  rcases hq with hq | hq <;> rcases hr with hr | hr
  · obtain ⟨j, hj, ht⟩ := ha
    exact ⟨j, hj, ht, outer_colored_mask q r hq hr j hj ht⟩
  · have h1 := hq.1 ⟨0, by omega⟩
    have h2 := hr.1 ⟨0, by omega⟩
    have h3 := hpar ⟨0, by omega⟩
    omega
  · have h1 := hq.1 ⟨0, by omega⟩
    have h2 := hr.1 ⟨0, by omega⟩
    have h3 := hpar ⟨0, by omega⟩
    omega
  · exact False.elim (central_colored_not_adjacent hp q r hq hr ha)
end RegisteredPrime
