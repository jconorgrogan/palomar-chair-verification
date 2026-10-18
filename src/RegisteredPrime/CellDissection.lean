module
public import RegisteredPrime.CompletedRules
@[expose] public section
namespace RegisteredPrime
open Uniform
abbrev Cell (p : Nat) := Fin p → Int
def bit (b : Bool) : Int := if b then 1 else 0
noncomputable def childCell (P : Parameters) (r : Role P.p) (x : Cell P.p) : Cell P.p :=
  fun i => childShift P r i +
    (if (childFrame P r).neg i.val then -1 else 1) * x (childIndex P r i) -
    (if (childFrame P r).neg i.val then 1 else 0)
def UnitChairCell {p : Nat} (x : Cell p) : Prop :=
  (∀ i, x i = 0 ∨ x i = 1) ∧ ∃ i, x i = 0
def DoubledChairCell {p : Nat} (x : Cell p) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 3) ∧ ∃ i, x i < 2
def CentralCell {p : Nat} (x : Cell p) : Prop :=
  (∀ i, x i = 1 ∨ x i = 2) ∧ ∃ i, x i = 1
def OuterCell {p : Nat} (A : Mask p) (x : Cell p) : Prop :=
  (∀ i, x i = 2 * bit (A i) ∨ x i = 2 * bit (A i) + 1) ∧
  ¬ (∀ i, x i = 1 + bit (A i))
@[simp] theorem outer_cell_formula (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (x : Cell P.p) (i : Fin P.p) :
    childCell P (.outer A hA) x i =
      if A i then 3 - x (childIndex P (.outer A hA) i)
      else x (childIndex P (.outer A hA) i) := by
  unfold childCell
  change (if A i then 4 else 0) +
    (if (outerFrame P A).neg i.val then -1 else 1) * x (childIndex P (.outer A hA) i) -
    (if (outerFrame P A).neg i.val then 1 else 0) = _
  rw [outerFrame_neg]
  cases A i <;> simp <;> omega
@[simp] theorem outer_cell_hole (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    childCell P (.outer A hA) (fun _ => 1) = fun i => 1 + bit (A i) := by
  funext i
  rw [outer_cell_formula]
  cases A i <;> rfl
@[simp] theorem central_cell_formula (P : Parameters) (x : Cell P.p) (i : Fin P.p) :
    childCell P .central x i = 1 + x (childIndex P .central i) := by
  simp [childCell, childShift, childFrame, scalarFrame]
theorem central_fills_outer_hole {p : Nat} (A : Mask p) (hA : Proper A) :
    CentralCell (fun i => 1 + bit (A i)) := by
  constructor
  · intro i
    cases h : A i <;> simp [bit, h]
  · obtain ⟨i, hi⟩ := hA
    exact ⟨i, by simp [bit, hi]⟩
theorem outer_image_cell (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (x : Cell P.p) (hx : UnitChairCell x) :
    OuterCell A (childCell P (.outer A hA) x) := by
  constructor
  · intro i
    rw [outer_cell_formula]
    obtain hi | hi := hx.1 (childIndex P (.outer A hA) i)
    all_goals cases ha : A i <;> simp [bit, hi]
  · intro hhole
    obtain ⟨j, hj⟩ := hx.2
    obtain ⟨i, hi⟩ := childIndex_surjective P (.outer A hA) j
    have h := hhole i
    rw [outer_cell_formula, hi, hj] at h
    cases ha : A i <;> simp [ha, bit] at h
theorem central_image_cell (P : Parameters) (x : Cell P.p) (hx : UnitChairCell x) :
    CentralCell (childCell P .central x) := by
  constructor
  · intro i
    rw [central_cell_formula]
    obtain hi | hi := hx.1 (childIndex P .central i) <;> simp [hi]
  · obtain ⟨j, hj⟩ := hx.2
    obtain ⟨i, hi⟩ := childIndex_surjective P .central j
    exact ⟨i, by rw [central_cell_formula, hi, hj]; rfl⟩
theorem outer_subset_doubled {p : Nat} (A : Mask p) (hA : Proper A)
    (x : Cell p) (hx : OuterCell A x) : DoubledChairCell x := by
  constructor
  · intro i
    have hi := hx.1 i
    cases ha : A i <;> simp [bit, ha] at hi <;> omega
  · obtain ⟨i, hi⟩ := hA
    have hc := hx.1 i
    simp [bit, hi] at hc
    exact ⟨i, by omega⟩
theorem central_subset_doubled {p : Nat} (x : Cell p) (hx : CentralCell x) :
    DoubledChairCell x := by
  constructor
  · intro i
    have hi := hx.1 i
    omega
  · obtain ⟨i, hi⟩ := hx.2
    exact ⟨i, by omega⟩
theorem outer_role_unique {p : Nat} {A B : Mask p} {x : Cell p}
    (hA : OuterCell A x) (hB : OuterCell B x) : A = B := by
  funext i
  have ha := hA.1 i
  have hb := hB.1 i
  cases h1 : A i <;> cases h2 : B i <;> simp [bit, h1, h2] at ha hb ⊢ <;> omega
theorem outer_central_disjoint {p : Nat} {A : Mask p} {x : Cell p}
    (ha : OuterCell A x) (hc : CentralCell x) : False := by
  apply ha.2
  intro i
  have h1 := ha.1 i
  have h2 := hc.1 i
  cases h : A i <;> simp [bit, h] at h1 ⊢ <;> omega
theorem doubled_cell_dissection {p : Nat} (x : Cell p) :
    DoubledChairCell x ↔ CentralCell x ∨ ∃ A : Mask p, Proper A ∧ OuterCell A x := by
  classical
  constructor
  · intro hx
    let A : Mask p := fun i => decide (2 ≤ x i)
    have hp : Proper A := by
      obtain ⟨i, hi⟩ := hx.2
      exact ⟨i, by simp [A]; omega⟩
    have hbox : ∀ i, x i = 2 * bit (A i) ∨ x i = 2 * bit (A i) + 1 := by
      intro i
      have hi := hx.1 i
      by_cases h : 2 ≤ x i <;> simp [A, bit, h] <;> omega
    by_cases hh : ∀ i, x i = 1 + bit (A i)
    · left
      have he : x = fun i => 1 + bit (A i) := funext hh
      rw [he]
      exact central_fills_outer_hole A hp
    · exact Or.inr ⟨A, hp, hbox, hh⟩
  · rintro (h | ⟨A, hp, h⟩)
    · exact central_subset_doubled x h
    · exact outer_subset_doubled A hp x h
end RegisteredPrime
