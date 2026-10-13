module

public import Uniform.Sign

@[expose] public section

/-! U2: parity / Sierpinski descent through outer children, any dimension `d`. -/
namespace Uniform

theorem foldl_induct {α β : Type} (f : β → α → β) (P : β → Prop) (l : List α) (b0 : β)
    (h0 : P b0) (hstep : ∀ b a, a ∈ l → P b → P (f b a)) : P (l.foldl f b0) := by
  induction l generalizing b0 with
  | nil => exact h0
  | cons a t ih =>
    simp only [List.foldl_cons]
    exact ih (f b0 a) (hstep b0 a List.mem_cons_self h0)
      (fun b a' ha' hb => hstep b a' (List.mem_cons_of_mem _ ha') hb)

theorem descend_append (child : (Nat → Bool) → Frame) (bs : List (Nat → Bool)) (b : Nat → Bool) :
    descend child (bs ++ [b]) = step child (descend child bs) b := by
  simp [descend, List.foldl_append]

/-- cell invariant: `T_i = 2 x_i + 2 [row i negative]` -/
def CellInv (st : Frame × (Nat → Int)) (i : Nat) : Prop :=
  st.2 i = 2 * cell st i + 2 * (if st.1.neg i then 1 else 0)

theorem step_cell (child : (Nat → Bool) → Frame) (st : Frame × (Nat → Int)) (b : Nat → Bool)
    (i : Nat) (hb : (child b).neg (st.1.perm i) = b (st.1.perm i)) (hinv : CellInv st i) :
    cell (step child st b) i = 2 * cell st i + (if worldDigit st.1 b i then 1 else 0) ∧
    CellInv (step child st b) i := by
  unfold CellInv at hinv ⊢
  have key : (step child st b).2 i - 2 * (if (step child st b).1.neg i then 1 else 0)
      = 2 * (2 * cell st i + (if worldDigit st.1 b i then 1 else 0)) := by
    simp only [step, Frame.comp, worldDigit, cornerT, hb]
    rw [hinv]
    generalize cell st i = Q
    by_cases hn : st.1.neg i <;> by_cases hb' : b (st.1.perm i) <;> simp [hn, hb'] <;> omega
  have hc : cell (step child st b) i = 2 * cell st i + (if worldDigit st.1 b i then 1 else 0) := by
    unfold cell; rw [key]; exact Int.mul_ediv_cancel_left _ (by decide)
  refine ⟨hc, ?_⟩
  rw [hc]; omega

/-- frames reached through proper children are rotations, and the cell invariant holds -/
theorem descend_good (d : Nat) (child : (Nat → Bool) → Frame) (bs : List (Nat → Bool))
    (hP : ProperChildren d child bs) :
    IsRotation d (descend child bs).1 ∧ ∀ i, i < d → CellInv (descend child bs) i := by
  apply foldl_induct (step child) (fun st => IsRotation d st.1 ∧ ∀ i, i < d → CellInv st i)
  · refine ⟨IsRotation.id d, fun i _ => ?_⟩
    simp [CellInv, cell, Frame.id]
  · rintro st b hb ⟨hrot, hinv⟩
    refine ⟨hrot.comp (hP b hb).1, fun i hi => ?_⟩
    exact (step_cell child st b i ((hP b hb).2 _ (hrot.1.1 i hi)) (hinv i hi)).2

/-- U2(a), geometry: the new binary digit of each cell coordinate is the world digit. -/
theorem U2a_cell_step (d : Nat) (child : (Nat → Bool) → Frame) (bs : List (Nat → Bool))
    (b : Nat → Bool) (hP : ProperChildren d child (bs ++ [b])) (i : Nat) (hi : i < d) :
    cell (descend child (bs ++ [b])) i
      = 2 * cell (descend child bs) i + (if worldDigit (descend child bs).1 b i then 1 else 0) := by
  have hP' : ProperChildren d child bs := fun b' hb' => hP b' (List.mem_append_left _ hb')
  have hb : b ∈ bs ++ [b] := List.mem_append_right _ List.mem_cons_self
  obtain ⟨hrot, hinv⟩ := descend_good d child bs hP'
  rw [descend_append]
  exact (step_cell child _ b i ((hP b hb).2 _ (hrot.1.1 i hi)) (hinv i hi)).1

/-- U2(a), parity: `#1s(world digit) ≡ |b| + #neg(parent)`. -/
theorem U2a_parity (d : Nat) (F : Frame) (hF : IsPermOn d F.perm) (b : Nat → Bool) :
    (List.range d).countP (worldDigit F b) % 2
      = ((List.range d).countP b + negCount d F.neg) % 2 := by
  unfold worldDigit negCount
  rw [countP_xor_mod, countP_comp_perm hF]

/-- U2(a), rotation parent: `#neg ≡ perm parity`. -/
theorem U2a_rotation (d : Nat) (F : Frame) (hF : IsRotation d F) :
    negCount d F.neg % 2 = invCount d F.perm % 2 := rotation_parity hF

/-! ### digits of the xor -/

theorem testBit_foldl_xor (x : Nat → Nat) (j : Nat) (l : List Nat) (a : Nat) :
    Nat.testBit (l.foldl (fun acc i => acc ^^^ x i) a) j
      = xor (Nat.testBit a j) (decide (l.countP (fun i => Nat.testBit (x i) j) % 2 = 1)) := by
  induction l generalizing a with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_xor, List.countP_cons]
    generalize (List.countP (fun i => Nat.testBit (x i) j) t) = C
    by_cases hc : C % 2 = 1 <;> cases Nat.testBit a j <;> cases Nat.testBit (x h) j <;>
      simp [hc] <;> omega

theorem testBit_xorAll (d : Nat) (x : Nat → Nat) (j : Nat) :
    Nat.testBit (xorAll d x) j = decide ((List.range d).countP (fun i => Nat.testBit (x i) j) % 2 = 1) := by
  unfold xorAll; rw [testBit_foldl_xor]; simp

theorem countP_congr_range {d : Nat} {f g : Nat → Bool} (h : ∀ i, i < d → f i = g i) :
    (List.range d).countP f = (List.range d).countP g := by
  apply List.countP_congr
  intro i hi; rw [h i (List.mem_range.1 hi)]

/-- sign form of the descent: digits of the xor are the parities of the number of negative signs
of the ancestor frames; and the cells lie in `[0, 2^N)`. -/
theorem descent_neg (d : Nat) (child : (Nat → Bool) → Frame) :
    ∀ rs : List (Nat → Bool), ProperChildren d child rs.reverse →
      (∀ i, i < d → 0 ≤ cell (descend child rs.reverse) i ∧
          cell (descend child rs.reverse) i < 2 ^ rs.length) ∧
      ∀ j, Nat.testBit (xorAll d (fun i => (cell (descend child rs.reverse) i).toNat)) j
        = (decide (j < rs.length) &&
           decide (negCount d (descend child (rs.reverse.take (rs.length - j))).1.neg % 2 = 1)) := by
  intro rs
  induction rs with
  | nil =>
    intro _
    refine ⟨fun i _ => ?_, fun j => ?_⟩
    · simp [descend, cell, Frame.id]
    · rw [testBit_xorAll]; simp [descend, cell, Frame.id]
  | cons b rs ih =>
    intro hP
    rw [List.reverse_cons] at hP ⊢
    simp only [List.length_cons]
    have hP' : ProperChildren d child rs.reverse :=
      fun b' hb' => hP b' (List.mem_append_left _ hb')
    obtain ⟨ihr, ihb⟩ := ih hP'
    obtain ⟨hrot, _⟩ := descend_good d child rs.reverse hP'
    have hstep := fun i hi => U2a_cell_step d child rs.reverse b hP i hi
    have hlen : rs.reverse.length = rs.length := List.length_reverse
    refine ⟨fun i hi => ?_, fun j => ?_⟩
    · rw [hstep i hi]
      have := ihr i hi
      rw [Int.pow_succ]
      split <;> omega
    · rw [testBit_xorAll]
      have hx : ∀ i, i < d → (cell (descend child (rs.reverse ++ [b])) i).toNat
          = 2 * (cell (descend child rs.reverse) i).toNat
            + (if worldDigit (descend child rs.reverse).1 b i then 1 else 0) := by
        intro i hi; rw [hstep i hi]; have := (ihr i hi).1; split <;> omega
      cases j with
      | zero =>
        have hc : (List.range d).countP
              (fun i => Nat.testBit (cell (descend child (rs.reverse ++ [b])) i).toNat 0)
            = (List.range d).countP (worldDigit (descend child rs.reverse).1 b) := by
          apply countP_congr_range
          intro i hi
          rw [hx i hi, Nat.testBit_zero]
          cases worldDigit (descend child rs.reverse).1 b i <;> simp <;> omega
        rw [hc]
        have h1 := U2a_parity d _ hrot.1 b
        have htake : (rs.reverse ++ [b]).take (rs.length + 1 - 0) = rs.reverse ++ [b] := by
          apply List.take_of_length_le; simp
        simp only [htake, descend_append]
        have h2 := negCount_comp d (descend child rs.reverse).1 (child b) hrot.1
        have h3 : negCount d (child b).neg = (List.range d).countP b :=
          countP_congr_range (fun i hi => (hP b (List.mem_append_right _ List.mem_cons_self)).2 i hi)
        rw [h3] at h2
        have e : (step child (descend child rs.reverse) b).1
            = (descend child rs.reverse).1.comp (child b) := rfl
        rw [e]
        simp only [Nat.zero_lt_succ, decide_true, Bool.true_and, decide_eq_decide]
        omega
      | succ j' =>
        have hc : (List.range d).countP
              (fun i => Nat.testBit (cell (descend child (rs.reverse ++ [b])) i).toNat (j' + 1))
            = (List.range d).countP
              (fun i => Nat.testBit (cell (descend child rs.reverse) i).toNat j') := by
          apply countP_congr_range
          intro i hi
          rw [hx i hi, Nat.testBit_add_one]
          congr 1; split <;> omega
        rw [hc, ← testBit_xorAll, ihb j']
        have ht : (rs.reverse ++ [b]).take (rs.length + 1 - (j' + 1)) = rs.reverse.take (rs.length - j') := by
          rw [show rs.length + 1 - (j' + 1) = rs.length - j' by omega]
          exact List.take_append_of_le_length (by simp)
        simp only [ht]
        simp

/-- U2(b), range: every cell coordinate of a depth-`N` tile lies in `[0, 2^N)`. -/
theorem U2b_cell_range (d : Nat) (child : (Nat → Bool) → Frame) (bs : List (Nat → Bool))
    (hP : ProperChildren d child bs) (i : Nat) (hi : i < d) :
    0 ≤ cell (descend child bs) i ∧ cell (descend child bs) i < 2 ^ bs.length := by
  have := (descent_neg d child bs.reverse (by simpa using hP)).1 i hi
  simpa using this

/-- U2(b): digit `k` (level `k = N - j`) of `x_1 xor … xor x_d` is the permutation parity of the
level-`k` ancestor frame; digits at positions `≥ N` vanish. -/
theorem U2b_descent (d : Nat) (child : (Nat → Bool) → Frame) (bs : List (Nat → Bool))
    (hP : ProperChildren d child bs) (j : Nat) :
    Nat.testBit (xorAll d (fun i => (cell (descend child bs) i).toNat)) j
      = (decide (j < bs.length) &&
         decide (invCount d (descend child (bs.take (bs.length - j))).1.perm % 2 = 1)) := by
  have := (descent_neg d child bs.reverse (by simpa using hP)).2 j
  simp only [List.reverse_reverse, List.length_reverse] at this
  rw [this]
  have hPk : ProperChildren d child (bs.take (bs.length - j)) :=
    fun b hb => hP b (List.mem_of_mem_take hb)
  rw [rotation_parity (descend_good d child _ hPk).1]

/-- U2(c): if every ancestor frame is an even permutation, the xor of the coordinates is 0. -/
theorem U2c_xor_zero (d : Nat) (child : (Nat → Bool) → Frame) (bs : List (Nat → Bool))
    (hP : ProperChildren d child bs)
    (heven : ∀ k, k ≤ bs.length → invCount d (descend child (bs.take k)).1.perm % 2 = 0) :
    xorAll d (fun i => (cell (descend child bs) i).toNat) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [U2b_descent d child bs hP j, Nat.zero_testBit, heven _ (by omega)]
  simp

end Uniform
