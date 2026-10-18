module

public import SparseMonotiles.CarrierHierarchyCells
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! The explicit alternating empty/central ancestor construction exhausts the
integer lattice. These are scaled undecorated carrier supports; legal leaf
patches and their physical realization are separate obligations. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- The anchor magnitude at even depth 2m, with binary digits 0,1,0,1,... . -/
def ancestorOffset : ℕ → ℤ
  | 0 => 0
  | m + 1 => ancestorOffset m + 2 * 4 ^ m

theorem ancestorOffset_formula (m : ℕ) : 3 * ancestorOffset m = 2 * 4 ^ m - 2 := by
  induction m with
  | zero => norm_num [ancestorOffset]
  | succ m ih => simp only [ancestorOffset, pow_succ]; nlinarith

theorem ancestorOffset_bounds (m : ℕ) :
    (m : ℤ) ≤ ancestorOffset m ∧ (m : ℤ) + 1 ≤ 4 ^ m - ancestorOffset m := by
  induction m with
  | zero => norm_num [ancestorOffset]
  | succ m ih =>
      have hp : 0 < (4 : ℤ) ^ m := pow_pos (by omega) m
      simp only [ancestorOffset, pow_succ, Nat.cast_add, Nat.cast_one]
      constructor <;> nlinarith [ih.1, ih.2]

/-- Unit cells of the level-2m carrier at anchor -ancestorOffset(m). -/
def AncestorCell {d : ℕ} (m : ℕ) (x : Cell d) : Prop :=
  (∀ i, -ancestorOffset m ≤ x i ∧ x i < 2 * 4 ^ m - ancestorOffset m) ∧
  ∃ i, x i < 4 ^ m - ancestorOffset m

theorem ancestorCell_mono {d : ℕ} {m : ℕ} {x : Cell d}
    (h : AncestorCell m x) : AncestorCell (m + 1) x := by
  have hp : 0 < (4 : ℤ) ^ m := pow_pos (by omega) m
  constructor
  · intro i
    obtain ⟨hl, hu⟩ := h.1 i
    simp only [ancestorOffset, pow_succ]
    constructor <;> nlinarith
  · obtain ⟨i, hi⟩ := h.2
    refine ⟨i, ?_⟩
    simp only [ancestorOffset, pow_succ]
    nlinarith

theorem box_in_ancestor {d : ℕ} (hd : 0 < d) (m : ℕ) (x : Cell d)
    (hx : ∀ i, -(m : ℤ) ≤ x i ∧ x i ≤ (m : ℤ)) : AncestorCell m x := by
  obtain ⟨hoff, hinner⟩ := ancestorOffset_bounds m
  have hp : 0 < (4 : ℤ) ^ m := pow_pos (by omega) m
  constructor
  · intro i
    obtain ⟨hl, hu⟩ := hx i
    constructor <;> linarith
  · let i : Fin d := ⟨0, hd⟩
    exact ⟨i, by linarith [(hx i).2]⟩

/-- Every integer cell eventually lies strictly below the omitted-corner
threshold of an alternating ancestor, in every coordinate. -/
theorem ancestorCell_exhaustive {d : ℕ} (hd : 0 < d) (x : Cell d) :
    ∃ m, AncestorCell m x := by
  let m : ℕ := ∑ i, (x i).natAbs
  refine ⟨m, box_in_ancestor hd m x ?_⟩
  intro i
  have hi : (x i).natAbs ≤ m := Finset.single_le_sum
    (fun j _ => Nat.zero_le ((x j).natAbs)) (Finset.mem_univ i)
  have hi' : ((x i).natAbs : ℤ) ≤ (m : ℤ) := by exact_mod_cast hi
  have hu : x i ≤ ((x i).natAbs : ℤ) := Int.le_natAbs
  have hl : -x i ≤ ((x i).natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -x i))
  constructor <;> omega

#print axioms ancestorOffset_formula
#print axioms ancestorCell_mono
#print axioms ancestorCell_exhaustive
end SparseMonotiles.CarrierHierarchy
