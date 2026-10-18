module

public import SparseMonotiles.ContactChairChecker

@[expose] public section

/-!
The exact undecorated-carrier hierarchy dissection. `DoubleCell` is the unit-cell
support of the doubled chair, not of a doubled keyed body. Outer index
permutations are arbitrary: coordinate permutations preserve the chair mask.
No contact completeness, recognizability, or physical registration is assumed.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

abbrev Bits (d : ℕ) := Fin d → Bool

def Proper {d : ℕ} (a : Bits d) : Prop := ∃ i, a i = false

def NonemptyRole {d : ℕ} (a : Bits d) : Prop := ∃ i, a i = true

def bit {d : ℕ} (a : Bits d) (i : Fin d) : ℤ := if a i then 1 else 0

def DoubleCell {d : ℕ} (x : Cell d) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 3) ∧ ∃ i, x i ≤ 1

def CentralCell {d : ℕ} (x : Cell d) : Prop :=
  (∀ i, x i = 1 ∨ x i = 2) ∧ ∃ i, x i = 1

/-- The box for role a, with its inward corner cell removed. -/
def OuterCell {d : ℕ} (a : Bits d) (x : Cell d) : Prop :=
  (∀ i, x i = 2 * bit a i ∨ x i = 2 * bit a i + 1) ∧
    x ≠ fun i => 1 + bit a i

def outerPose {d : ℕ} (a : Bits d) (σ : Equiv.Perm (Fin d)) : Pose d where
  perm := σ
  negative := a
  shift := fun i => 4 * bit a i

def centralPose (d : ℕ) : Pose d where
  perm := Equiv.refl _
  negative := fun _ => false
  shift := fun _ => 1

/-- Occupied integer unit cells of an actual registered chair pose. -/
def Occupies {d : ℕ} (p : Pose d) (x : Cell d) : Prop :=
  IsChairCell (p.inverseCell x)

@[simp] theorem occupies_central {d : ℕ} (x : Cell d) :
    Occupies (centralPose d) x ↔ CentralCell x := by
  simp only [Occupies, IsChairCell, Pose.inverseCell, centralPose, Pose.sign,
    Bool.false_eq_true, if_false, Equiv.refl_symm, Equiv.refl_apply,
    mul_one, one_mul, add_zero]
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨fun j => by rcases h j with h | h <;> omega, i, by omega⟩
  · rintro ⟨h, i, hi⟩
    exact ⟨fun j => by rcases h j with h | h <;> omega, i, by omega⟩

private theorem outer_inverse_at {d : ℕ} (a : Bits d)
    (σ : Equiv.Perm (Fin d)) (x : Cell d) (i : Fin d) :
    (outerPose a σ).inverseCell x (σ i) =
      if a i then 3 - x i else x i := by
  simp only [Pose.inverseCell, outerPose, Equiv.symm_apply_apply, Pose.sign]
  cases h : a i <;> simp [bit, h] <;> omega

/-- Binding the geometric role formula to the checker's genuine cell action. -/
theorem occupies_outer {d : ℕ} (a : Bits d) (σ : Equiv.Perm (Fin d))
    (x : Cell d) : Occupies (outerPose a σ) x ↔ OuterCell a x := by
  constructor
  · rintro ⟨h, ⟨j, hj⟩⟩
    constructor
    · intro i
      have hi := h (σ i)
      rw [outer_inverse_at] at hi
      cases ha : a i <;> simp [ha, bit] at hi ⊢ <;> omega
    · intro he
      obtain ⟨i, rfl⟩ := σ.surjective j
      rw [outer_inverse_at] at hj
      have hi := congrFun he i
      cases ha : a i <;> simp [ha, bit] at hi hj <;> omega
  · rintro ⟨h, hn⟩
    constructor
    · intro j
      obtain ⟨i, rfl⟩ := σ.surjective j
      rw [outer_inverse_at]
      have hi := h i
      cases ha : a i <;> simp [ha, bit] at hi ⊢ <;> omega
    · have hn' : ∃ i, x i ≠ 1 + bit a i := by
        by_contra hh
        apply hn
        funext i
        by_contra hi
        exact hh ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hn'
      refine ⟨σ i, ?_⟩
      rw [outer_inverse_at]
      have hb := h i
      cases ha : a i <;> simp [ha, bit] at hi hb ⊢ <;> omega

theorem centralCell_double {d : ℕ} {x : Cell d} (h : CentralCell x) :
    DoubleCell x := by
  obtain ⟨hb, i, hi⟩ := h
  exact ⟨fun j => by rcases hb j with h | h <;> omega, i, by omega⟩

theorem outerCell_double {d : ℕ} {a : Bits d} (ha : Proper a)
    {x : Cell d} (h : OuterCell a x) : DoubleCell x := by
  obtain ⟨i, hi⟩ := ha
  constructor
  · intro j
    have hj := h.1 j
    cases hb : a j <;> simp [bit, hb] at hj <;> omega
  · refine ⟨i, ?_⟩
    have hx := h.1 i
    simp [bit, hi] at hx
    omega

/-- Distinct corner boxes are disjoint; this does not use decoration or frames. -/
theorem outer_role_unique {d : ℕ} {a b : Bits d} {x : Cell d}
    (ha : OuterCell a x) (hb : OuterCell b x) : a = b := by
  funext i
  have ha' := ha.1 i
  have hb' := hb.1 i
  cases h₁ : a i <;> cases h₂ : b i <;>
    simp [bit, h₁, h₂] at ha' hb' ⊢ <;> omega

theorem central_outer_disjoint {d : ℕ} {a : Bits d} {x : Cell d}
    (hc : CentralCell x) (ha : OuterCell a x) : False := by
  apply ha.2
  funext i
  have hc' := hc.1 i
  have ha' := ha.1 i
  cases hb : a i <;> simp [bit, hb] at ha' ⊢ <;> omega

/-- Exact coverage: the missing inward corner in each outer box is supplied by
one central chair. The all-one outer role is absent, as required. -/
theorem doubleCell_iff {d : ℕ} (x : Cell d) :
    DoubleCell x ↔ CentralCell x ∨ ∃ a, Proper a ∧ OuterCell a x := by
  constructor
  · intro h
    let a : Bits d := fun i => decide (2 ≤ x i)
    have ha : Proper a := by
      obtain ⟨i, hi⟩ := h.2
      exact ⟨i, by simp [a]; omega⟩
    have hb : ∀ i, x i = 2 * bit a i ∨ x i = 2 * bit a i + 1 := by
      intro i
      have hi := h.1 i
      by_cases hx : 2 ≤ x i <;> simp [bit, a, hx] <;> omega
    by_cases he : x = fun i => 1 + bit a i
    · left
      constructor
      · intro i
        have hi := congrFun he i
        cases ha' : a i <;> simp [bit, ha'] at hi <;> omega
      · obtain ⟨i, hi⟩ := ha
        exact ⟨i, by have hx := congrFun he i; simpa [bit, hi] using hx⟩
    · exact Or.inr ⟨a, ha, hb, he⟩
  · rintro (hc | ⟨a, ha, hx⟩)
    · exact centralCell_double hc
    · exact outerCell_double ha hx

/-- Complete exact one-level dissection, stated in the registered pose API. -/
theorem canonical_dissection {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (x : Cell d) :
    DoubleCell x ↔ Occupies (centralPose d) x ∨
      ∃ a, Proper a ∧ Occupies (outerPose a (σ a)) x := by
  simp_rw [occupies_central, occupies_outer]
  exact doubleCell_iff x

#print axioms occupies_outer
#print axioms canonical_dissection
#print axioms outer_role_unique
#print axioms central_outer_disjoint
end SparseMonotiles.CarrierHierarchy
