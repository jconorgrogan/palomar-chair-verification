module
public import RegisteredPrime.CoarseAlignment
@[expose] public section
namespace RegisteredPrime

def shiftCell {p : Nat} (c : Cell p) (j : Fin p) (n : Int) : Cell p :=
  fun i => c i + if i = j then n else 0

@[simp] theorem shiftCell_zero {p : Nat} (c : Cell p) (j : Fin p) : shiftCell c j 0 = c := by
  funext i
  simp [shiftCell]

theorem shiftCell_adjacent {p : Nat} (c : Cell p) (j : Fin p) (n m : Int)
    (h : n = m + 1 ∨ m = n + 1) : Adjacent (shiftCell c j n) (shiftCell c j m) := by
  refine ⟨j, ?_, ?_⟩
  · simp [shiftCell]
    omega
  · intro i hij
    simp [shiftCell, hij]

theorem cell_property_shift {p : Nat} (F : Cell p → Prop)
    (hstep : ∀ a b, Adjacent a b → F a → F b)
    (c : Cell p) (hc : F c) (j : Fin p) (z : Int) : F (shiftCell c j z) := by
  have hpos : ∀ n : Nat, F (shiftCell c j (n : Int)) := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ih =>
      exact hstep _ _ (shiftCell_adjacent c j (n : Int) ((n + 1 : Nat) : Int)
        (Or.inr (by omega))) ih
  have hneg : ∀ n : Nat, F (shiftCell c j (-(n : Int))) := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ih =>
      exact hstep _ _ (shiftCell_adjacent c j (-(n : Int)) (-((n + 1 : Nat) : Int))
        (Or.inl (by omega))) ih
  cases z with
  | ofNat n => exact hpos n
  | negSucc n => exact hneg (n + 1)

/-- The integer cell grid is face-connected, proved by finite coordinate
replacement and integer unit steps. No topological connectedness is assumed. -/
theorem cell_property_global {p : Nat} (F : Cell p → Prop)
    (hstep : ∀ a b, Adjacent a b → F a → F b)
    (c : Cell p) (hc : F c) (d : Cell p) : F d := by
  let patch : Nat → Cell p := fun n i => if i.val < n then d i else c i
  have hpatch : ∀ n, n ≤ p → F (patch n) := by
    intro n
    induction n with
    | zero =>
      intro _
      have he : patch 0 = c := by funext i; simp [patch]
      rwa [he]
    | succ n ih =>
      intro hnp
      have hn : n < p := by omega
      let j : Fin p := ⟨n, hn⟩
      have he : patch (n + 1) = shiftCell (patch n) j (d j - c j) := by
        funext i
        by_cases hij : i = j
        · subst i
          simp [patch, shiftCell, j]
          omega
        · have hne : i.val ≠ n := by
            intro hei
            exact hij (Fin.ext hei)
          by_cases hlt : i.val < n
          · have hlt' : i.val < n + 1 := by omega
            simp [patch, shiftCell, hij, hlt, hlt']
          · have hlt' : ¬ i.val < n + 1 := by omega
            simp [patch, shiftCell, hij, hlt, hlt']
      rw [he]
      exact cell_property_shift F hstep (patch n) (ih (by omega)) j _
  have he : patch p = d := by
    funext i
    simp [patch, i.isLt]
  have h := hpatch p (Nat.le_refl p)
  rwa [he] at h

end RegisteredPrime
