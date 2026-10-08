module
public import RegisteredPrime.ContactParity
@[expose] public section
namespace RegisteredPrime
def boxLower {p : Nat} (q : Pose p) : Cell p :=
  fun i => q.anchor i - 2 * bit (q.frame.negative i)
def hole {p : Nat} (q : Pose p) : Cell p := q.cell (fun _ => 1)
@[simp] theorem hole_coordinate {p : Nat} (q : Pose p) (i : Fin p) :
    hole q i = q.anchor i + 1 - 3 * bit (q.frame.negative i) := by
  simp only [hole, Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, bit]
  by_cases hn : q.frame.negative i = true <;> simp [hn] <;> omega
@[simp] theorem Pose.inv_cell_cell {p : Nat} (q : Pose p) (c : Cell p) :
    q.inv.cell (q.cell c) = c := by
  funext i
  simp only [Pose.inv, Pose.cell, RegisteredFrame.linear, RegisteredFrame.inv,
    RegisteredFrame.sign, q.frame.right_inverse, bit]
  by_cases hn : q.frame.negative (q.frame.inverse i) = true <;> simp [hn] <;> omega
@[simp] theorem Pose.cell_inv_cell {p : Nat} (q : Pose p) (c : Cell p) :
    q.cell (q.inv.cell c) = c := by
  funext i
  simp only [Pose.inv, Pose.cell, RegisteredFrame.linear, RegisteredFrame.inv,
    RegisteredFrame.sign, q.frame.left_inverse, bit]
  by_cases hn : q.frame.negative i = true <;> simp [hn] <;> omega
theorem occupies_inverse_iff {p : Nat} (q : Pose p) (c : Cell p) :
    Occupies q c ↔ UnitChairCell (q.inv.cell c) := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa using hb
  · intro h
    exact ⟨q.inv.cell c, h, q.cell_inv_cell c⟩
theorem inverse_at {p : Nat} (q : Pose p) (x : Cell p) (i : Fin p) :
    q.inv.cell x (q.frame.perm i) =
      if q.frame.negative i then q.anchor i - 1 - x i else x i - q.anchor i := by
  simp only [Pose.inv, Pose.cell, RegisteredFrame.linear, RegisteredFrame.inv,
    RegisteredFrame.sign, q.frame.left_inverse, bit]
  by_cases hn : q.frame.negative i = true <;> simp [hn] <;> omega
theorem occupies_box_iff {p : Nat} (q : Pose p) (x : Cell p) :
    Occupies q x ↔
      (∀ i, x i = boxLower q i ∨ x i = boxLower q i + 1) ∧ x ≠ hole q := by
  rw [occupies_inverse_iff]
  constructor
  · rintro ⟨h, j, hj⟩
    constructor
    · intro i
      have hi := h (q.frame.perm i)
      rw [inverse_at] at hi
      by_cases hn : q.frame.negative i = true <;> simp [boxLower, bit, hn] at hi ⊢ <;> omega
    · intro he
      let i := q.frame.inverse j
      have hij : q.frame.perm i = j := q.frame.right_inverse j
      rw [← hij, inverse_at] at hj
      have hi := congrFun he i
      rw [hole_coordinate] at hi
      by_cases hn : q.frame.negative i = true <;> simp [hn, bit] at hi hj <;> omega
  · rintro ⟨h, hn⟩
    have hdigits : ∀ j, q.inv.cell x j = 0 ∨ q.inv.cell x j = 1 := by
      intro j
      let i := q.frame.inverse j
      have hij : q.frame.perm i = j := q.frame.right_inverse j
      rw [← hij, inverse_at]
      have hi := h i
      by_cases hn : q.frame.negative i = true <;> simp [boxLower, bit, hn] at hi ⊢ <;> omega
    refine ⟨hdigits, ?_⟩
    apply Classical.byContradiction
    intro hz
    apply hn
    have hone : q.inv.cell x = fun _ => 1 := by
      funext j
      obtain h | h := hdigits j
      · exact False.elim (hz ⟨j, h⟩)
      · exact h
    have he := congrArg q.cell hone
    simpa [hole] using he
def exterior {p : Nat} (A : Mask p) (j : Fin p) : Cell p :=
  fun i => bit (A i) + if i = j then 2 * bit (A j) - 1 else 0
def wallBox {p : Nat} (j : Fin p) (b : Bool) : Cell p :=
  fun i => if i = j then if b then 2 else -2 else 0
theorem even_exterior_box {p : Nat} (q : Pose p) (A : Mask p) (j : Fin p)
    (hq : Occupies q (exterior A j)) (he : ∀ i, boxLower q i % 2 = 0) :
    boxLower q = wallBox j (A j) := by
  funext i
  have hb := ((occupies_box_iff q _).mp hq).1 i
  have hi := he i
  by_cases hij : i = j
  · subst i
    cases ha : A j <;> simp [exterior, wallBox, bit, ha] at hb ⊢ <;> omega
  · cases ha : A i <;> simp [exterior, wallBox, bit, ha, hij] at hb ⊢ <;> omega
theorem odd_exterior_box {p : Nat} (q : Pose p) (A : Mask p) (j : Fin p)
    (hq : Occupies q (exterior A j)) (ho : ∀ i, boxLower q i % 2 = 1) :
    boxLower q = fun i => 2 * bit (A i) - 1 := by
  funext i
  have hb := ((occupies_box_iff q _).mp hq).1 i
  have hi := ho i
  by_cases hij : i = j
  · subst i
    cases ha : A j <;> simp [exterior, bit, ha] at hb ⊢ <;> omega
  · cases ha : A i <;> simp [exterior, bit, ha, hij] at hb ⊢ <;> omega
theorem odd_exterior_hole {p : Nat} (q : Pose p) (A : Mask p) (j : Fin p)
    (hq : Occupies q (exterior A j)) (ho : ∀ i, boxLower q i % 2 = 1)
    (hn : ¬ Occupies q (fun i => bit (A i))) : hole q = fun i => bit (A i) := by
  have hb := odd_exterior_box q A j hq ho
  apply Classical.byContradiction
  intro hne
  apply hn
  apply (occupies_box_iff q _).mpr
  constructor
  · intro i
    rw [congrFun hb i]
    cases A i <;> simp [bit]
  · exact fun h => hne h.symm
theorem uniform_parity_box {p : Nat} (q : Pose p) (b : Bool)
    (hq : ∀ i, q.anchor i % 2 = bit b) : ∀ i, boxLower q i % 2 = bit b := by
  intro i
  have h := hq i
  cases b <;> cases hn : q.frame.negative i <;> simp [boxLower, bit, hn] at h ⊢ <;> omega
end RegisteredPrime
