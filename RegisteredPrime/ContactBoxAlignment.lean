module
public import RegisteredPrime.DyadicCarrierColor
@[expose] public section
namespace RegisteredPrime
@[simp] theorem hole_from_box {p : Nat} (q : Pose p) (i : Fin p) :
    hole q i = boxLower q i + 1 - bit (q.frame.negative i) := by
  rw [hole_coordinate]
  simp only [boxLower]
  omega
theorem same_box_overlap {p : Nat} (q r : Pose p) (i j : Fin p) (hij : i ≠ j)
    (hbox : boxLower q = boxLower r) : ∃ c, Occupies q c ∧ Occupies r c := by
  classical
  let c : Cell p := fun k => boxLower q k +
    if k = i then bit (q.frame.negative i) else if k = j then bit (r.frame.negative j) else 0
  have hb : ∀ k, c k = boxLower q k ∨ c k = boxLower q k + 1 := by
    intro k
    by_cases hki : k = i
    · subst k
      cases hn : q.frame.negative i <;> simp [c, bit, hn]
    · by_cases hkj : k = j
      · subst k
        cases hn : r.frame.negative j <;> simp [c, bit, hn, hki]
      · simp [c, hki, hkj]
  refine ⟨c, (occupies_box_iff q c).mpr ⟨hb, ?_⟩,
    (occupies_box_iff r c).mpr ⟨fun k => by rw [← hbox]; exact hb k, ?_⟩⟩
  · intro h
    have hi := congrFun h i
    rw [hole_from_box] at hi
    cases hn : q.frame.negative i <;> simp [c, bit, hn] at hi <;> omega
  · intro h
    have hj := congrFun h j
    rw [hole_from_box, ← hbox] at hj
    have hji : j ≠ i := fun he => hij he.symm
    cases hn : r.frame.negative j <;> simp [c, bit, hn, hji] at hj <;> omega
def BoxAdjacent {p : Nat} (q r : Pose p) : Prop := ∃ j,
  (boxLower r j = boxLower q j + 2 ∨ boxLower q j = boxLower r j + 2) ∧
  ∀ i, i ≠ j → boxLower q i = boxLower r i
theorem contact_box_adjacent {p : Nat} (hp : 3 ≤ p) (q r : Pose p)
    (hc : FaceContact q r)
    (hpar : ∀ i, boxLower q i % 2 = boxLower r i % 2) : BoxAdjacent q r := by
  obtain ⟨hd, a, b, hqa, hrb, j, hj, hab⟩ := hc
  have hq := (occupies_box_iff q a).mp hqa
  have hr := (occupies_box_iff r b).mp hrb
  have htrans : ∀ i, i ≠ j → boxLower q i = boxLower r i := by
    intro i hi
    have h1 := hq.1 i
    have h2 := hr.1 i
    have h3 := hab i hi
    have h4 := hpar i
    omega
  have hdiff : boxLower r j = boxLower q j + 2 ∨
      boxLower q j = boxLower r j ∨ boxLower q j = boxLower r j + 2 := by
    have h1 := hq.1 j
    have h2 := hr.1 j
    have h3 := hpar j
    omega
  refine ⟨j, ?_, htrans⟩
  rcases hdiff with h | h | h
  · exact Or.inl h
  · have he : boxLower q = boxLower r := by
      funext i
      by_cases hi : i = j
      · exact hi ▸ h
      · exact htrans i hi
    have hi : (⟨0, by omega⟩ : Fin p) ≠ ⟨1, by omega⟩ := by
      intro h
      have hv := congrArg Fin.val h
      change (0 : Nat) = 1 at hv
      omega
    obtain ⟨c, hqc, hrc⟩ := same_box_overlap q r ⟨0, by omega⟩ ⟨1, by omega⟩ hi he
    exact False.elim (hd c ⟨hqc, hrc⟩)
  · exact Or.inr h
@[simp] theorem relative_negative {p : Nat} (q r : Pose p) (i : Fin p) :
    (q.relative r).frame.negative i =
      xor (q.frame.negative (q.frame.inverse i)) (r.frame.negative (q.frame.inverse i)) := rfl
theorem relative_anchor {p : Nat} (q r : Pose p) (i : Fin p) :
    (q.relative r).anchor i = q.frame.sign (q.frame.inverse i) *
      (r.anchor (q.frame.inverse i) - q.anchor (q.frame.inverse i)) := by
  simp only [Pose.relative, Pose.comp, Pose.inv, RegisteredFrame.linear,
    RegisteredFrame.inv, RegisteredFrame.sign]
  by_cases hn : q.frame.negative (q.frame.inverse i) = true <;> simp [hn] <;> omega
theorem relative_boxLower {p : Nat} (q r : Pose p) (i : Fin p) :
    boxLower (q.relative r) i = q.frame.sign (q.frame.inverse i) *
      (boxLower r (q.frame.inverse i) - boxLower q (q.frame.inverse i)) := by
  simp only [boxLower, relative_anchor, relative_negative, RegisteredFrame.sign, bit]
  by_cases hn : q.frame.negative (q.frame.inverse i) = true <;>
    by_cases hm : r.frame.negative (q.frame.inverse i) = true <;> simp [hn, hm] <;> omega
theorem even_relative_box_parity {p : Nat} (q r : Pose p)
    (he : ∀ i, (q.relative r).anchor i % 2 = 0) :
    ∀ i, boxLower q i % 2 = boxLower r i % 2 := by
  intro i
  have h := he (q.frame.perm i)
  rw [relative_anchor, q.frame.left_inverse] at h
  simp only [boxLower]
  by_cases hn : q.frame.negative i = true <;> simp [RegisteredFrame.sign, hn] at h <;> omega
end RegisteredPrime
