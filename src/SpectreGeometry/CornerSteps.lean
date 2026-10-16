module

public import SpectreGeometry.RotationData

@[expose] public section


/-! Exact corner-turn catalogue in the cyclic twelve-direction model.
The step counts are combinatorial angle data; applying them to arbitrary
physical tiling germs requires a separate geometric correspondence. -/
namespace SpectreGeometry

def previous (i : Fin 14) : Fin 14 := ⟨(i.val+13)%14,Nat.mod_lt _ (by decide)⟩
def cornerSteps (i : Fin 14) : Nat :=
  (18+(edgeTurn (previous i)).val-(edgeTurn i).val)%12

theorem corner_steps_table : (List.finRange 14).map cornerSteps =
    [3,8,3,4,9,4,3,4,9,4,6,4,3,8] := by decide

theorem corner_steps_values : ∀ i : Fin 14,
    cornerSteps i = 3 ∨ cornerSteps i = 4 ∨ cornerSteps i = 6 ∨
      cornerSteps i = 8 ∨ cornerSteps i = 9 := by decide

theorem corner_steps_minimum : ∀ i : Fin 14, 3 ≤ cornerSteps i := by decide

theorem unique_straight_corner : ∀ i : Fin 14, cornerSteps i = 6 ↔ i = 10 := by decide

theorem straight_corner_neighbors : cornerSteps (previous 10) = 4 ∧ cornerSteps (next 10) = 4 := by decide

theorem right_corner_neighbors : ∀ i : Fin 14, cornerSteps i = 3 →
    4 ≤ cornerSteps (previous i) ∧ 4 ≤ cornerSteps (next i) := by decide

private theorem sum_minimum (l : List Nat) (h : ∀ a ∈ l, 3 ≤ a) : 3*l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := h a (by simp)
      have hl := ih (fun b hb => h b (by simp [hb]))
      simp only [List.length_cons,List.sum_cons,Nat.mul_add,Nat.mul_one]
      omega

/-- A half-turn partition by sectors of at least three steps can only be
one straight sector or two right sectors. This is a numerical lemma only. -/
theorem halfturn_partition (l : List Nat) (hmin : ∀ a ∈ l, 3 ≤ a) (hs : l.sum = 6) :
    l = [6] ∨ l = [3,3] := by
  have hl := sum_minimum l hmin
  cases l with
  | nil => simp at hs
  | cons a l =>
      have ha := hmin a (by simp)
      cases l with
      | nil =>
          have he : a = 6 := by simpa using hs
          exact Or.inl (by subst a; rfl)
      | cons b l =>
          have hb := hmin b (by simp)
          have hlen : l.length = 0 := by
            simp only [List.length_cons] at hl
            omega
          have he : l = [] := List.eq_nil_of_length_eq_zero hlen
          subst l
          simp only [List.sum_cons,List.sum_nil] at hs
          have heqa : a = 3 := by omega
          have heqb : b = 3 := by omega
          exact Or.inr (by subst a; subst b; rfl)

end SpectreGeometry
