module
public import Uniform.U4
@[expose] public section
namespace RegisteredPrime.MeanObstruction
open Uniform

/-- Symmetric difference of bounded Boolean masks. -/
def symmDiff (A B : Nat → Bool) : Nat → Bool := fun i => xor (A i) (B i)
def singleton (j : Nat) : Nat → Bool := fun i => decide (i = j)
def toggle (A : Nat → Bool) (j : Nat) : Nat → Bool := symmDiff (singleton j) A

theorem card_congr {p : Nat} {A B : Nat → Bool}
    (h : ∀ i, i < p → A i = B i) : suppCard p A = suppCard p B :=
  countP_congr_range h

theorem sum_congr {p : Nat} {A B : Nat → Bool}
    (h : ∀ i, i < p → A i = B i) : suppSum p A = suppSum p B := by
  unfold suppSum
  rw [filter_sum_eq, filter_sum_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem mean_congr {p : Nat} {A B : Nat → Bool}
    (h : ∀ i, i < p → A i = B i) : zA p A = zA p B := by
  unfold zA
  rw [card_congr h, sum_congr h]

theorem card_empty (p : Nat) : suppCard p (fun _ => false) = 0 := by
  simp [suppCard]
theorem sum_empty (p : Nat) : suppSum p (fun _ => false) = 0 := by
  unfold suppSum
  generalize List.range p = l
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.filter_cons, Bool.false_eq_true, ite_false] using ih

/-- Integer cardinality as a sum of indicator functions. -/
theorem card_as_sum (l : List Nat) (A : Nat → Bool) :
    (l.countP A : Int) = (l.map (fun i => if A i then (1 : Int) else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    cases A a <;> simp [ih] <;> omega

theorem sum_as_sum (p : Nat) (A : Nat → Bool) :
    (suppSum p A : Int) =
      ((List.range p).map (fun i => if A i then (i : Int) else 0)).sum := by
  unfold suppSum
  rw [filter_sum_eq, natCast_sum]
  congr 1
  apply List.map_congr_left
  intro i _
  cases A i <;> simp

theorem sum_update (l : List Nat) (hnd : l.Nodup) (j : Nat) (hj : j ∈ l)
    (f : Nat → Int) (c : Int) :
    (l.map (fun i => if i = j then c else f i)).sum = (l.map f).sum + c - f j := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases ha : a = j
    · subst a
      have he : l.map (fun i => if i = j then c else f i) = l.map f := by
        apply List.map_congr_left
        intro i hi
        have : i ≠ j := by intro e; subst i; exact hnd.1 hi
        simp [this]
      simp only [ite_true, he]
      omega
    · have hj' : j ∈ l := by simpa [ha, Ne.symm ha] using hj
      rw [ite_eq_right ha, ih hnd.2 hj']
      omega

theorem card_toggle {p j : Nat} (hj : j < p) (A : Nat → Bool) :
    (suppCard p (toggle A j) : Int) = (suppCard p A : Int) +
      (if A j then -1 else 1) := by
  unfold suppCard
  rw [card_as_sum, card_as_sum]
  have he :
      (List.range p).map (fun i => if toggle A j i then (1 : Int) else 0) =
      (List.range p).map (fun i => if i = j then (if A j then 0 else 1)
        else (if A i then 1 else 0)) := by
    apply List.map_congr_left
    intro i _
    by_cases h : i = j
    · subst i; cases hAj : A j <;> simp [toggle, symmDiff, singleton, hAj]
    · simp [toggle, symmDiff, singleton, h]
  rw [he, sum_update _ List.nodup_range j (List.mem_range.mpr hj)]
  cases A j <;> simp <;> omega

theorem sum_toggle {p j : Nat} (hj : j < p) (A : Nat → Bool) :
    (suppSum p (toggle A j) : Int) = (suppSum p A : Int) +
      (if A j then -(j : Int) else j) := by
  rw [sum_as_sum, sum_as_sum]
  have he :
      (List.range p).map (fun i => if toggle A j i then (i : Int) else 0) =
      (List.range p).map (fun i => if i = j then (if A j then 0 else (j : Int))
        else (if A i then i else 0)) := by
    apply List.map_congr_left
    intro i _
    by_cases h : i = j
    · subst i; cases hAj : A j <;> simp [toggle, symmDiff, singleton, hAj]
    · simp [toggle, symmDiff, singleton, h]
  rw [he, sum_update _ List.nodup_range j (List.mem_range.mpr hj)]
  cases A j <;> simp <;> omega

theorem card_singleton {p j : Nat} (hj : j < p) : suppCard p (singleton j) = 1 := by
  have h := card_toggle hj (fun _ => false)
  have he : toggle (fun _ => false) j = singleton j := by
    funext i; simp [toggle, symmDiff]
  rw [he, card_empty] at h
  simp at h
  omega

theorem sum_singleton {p j : Nat} (hj : j < p) : suppSum p (singleton j) = j := by
  have h := sum_toggle hj (fun _ => false)
  have he : toggle (fun _ => false) j = singleton j := by
    funext i; simp [toggle, symmDiff]
  rw [he, sum_empty] at h
  simp at h
  omega

theorem exists_other {p j : Nat} (hp : 2 ≤ p) (_hj : j < p) :
    ∃ x, x < p ∧ x ≠ j := by
  by_cases h : j = 0
  · exact ⟨1, by omega, by omega⟩
  · exact ⟨0, by omega, Ne.symm h⟩

theorem exists_third {p j x : Nat} (hp : 3 ≤ p) (_hj : j < p) (_hx : x < p) :
    ∃ y, y < p ∧ y ≠ j ∧ y ≠ x := by
  by_cases hj0 : j = 0 <;> by_cases hx0 : x = 0 <;>
    by_cases hj1 : j = 1 <;> by_cases hx1 : x = 1
  all_goals first
    | exact ⟨0, by omega, by omega, by omega⟩
    | exact ⟨1, by omega, by omega, by omega⟩
    | exact ⟨2, by omega, by omega, by omega⟩

theorem singleton_proper {p j : Nat} (hp : 2 ≤ p) (hj : j < p) :
    NonemptyProperOn p (singleton j) := by
  obtain ⟨x, hx, hne⟩ := exists_other hp hj
  exact ⟨⟨j, hj, by simp [singleton]⟩, ⟨x, hx, by simp [singleton, hne]⟩⟩

/-- Two distinct residues, represented without a finset dependency. -/
def pair (j x : Nat) : Nat → Bool := toggle (singleton j) x

theorem pair_at_left {j x : Nat} (h : j ≠ x) : pair j x j = true := by
  simp [pair, toggle, symmDiff, singleton, h]
theorem pair_at_right {j x : Nat} (h : j ≠ x) : pair j x x = true := by
  simp [pair, toggle, symmDiff, singleton, Ne.symm h]

theorem pair_proper {p j x : Nat} (hp : 3 ≤ p) (hj : j < p) (hx : x < p)
    (hne : j ≠ x) : NonemptyProperOn p (pair j x) := by
  obtain ⟨y, hy, hyj, hyx⟩ := exists_third hp hj hx
  exact ⟨⟨j, hj, pair_at_left hne⟩,
    ⟨y, hy, by simp [pair, toggle, symmDiff, singleton, hyj, hyx]⟩⟩

theorem card_pair {p j x : Nat} (hj : j < p) (hx : x < p) (hne : j ≠ x) :
    suppCard p (pair j x) = 2 := by
  have h := card_toggle hx (singleton j)
  rw [card_singleton hj] at h
  simp only [singleton, Ne.symm hne, decide_false, Bool.false_eq_true, ite_false] at h
  change (suppCard p (pair j x) : Int) = _ at h
  omega

theorem sum_pair {p j x : Nat} (hj : j < p) (hx : x < p) (hne : j ≠ x) :
    suppSum p (pair j x) = j + x := by
  have h := sum_toggle hx (singleton j)
  rw [sum_singleton hj] at h
  simp only [singleton, Ne.symm hne, decide_false, Bool.false_eq_true, ite_false] at h
  change (suppSum p (pair j x) : Int) = _ at h
  omega

/-- The defining finite-field mean equation, in the congruence API. -/
theorem mean_equation {p : Nat} (hp : IsPrime p) (A : Nat → Bool)
    (hA : NonemptyProperOn p A) :
    MEq p ((suppCard p A : Int) * zA p A) (suppSum p A) := by
  have h := MEq.of_nat_mod (U1_zA p hp A hA).2.1
  simpa only [Int.natCast_mul] using h

theorem mean_singleton {p j : Nat} (hp : IsPrime p) (hj : j < p) :
    zA p (singleton j) = j := by
  obtain ⟨hzlt, _, hzuniq⟩ := U1_zA p hp (singleton j) (singleton_proper hp.two_le hj)
  apply Eq.symm
  apply hzuniq j hj
  rw [card_singleton hj, sum_singleton hj, Nat.one_mul]

end RegisteredPrime.MeanObstruction
