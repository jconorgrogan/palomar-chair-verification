module

public import Init

@[expose] public section


/-! Elementary quantitative separation of the exact area factor seven and
boundary factor six. The later geometric hierarchy must supply the stated
cardinality bounds; this arithmetic module does not postulate a hierarchy. -/
namespace SpectreFinite.AreaBoundaryGrowth

theorem bernoulli_seven_six (n : Nat) : (n+6)*6^n ≤ 6*7^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      (n+1+6)*6^(n+1) = (6*(n+1+6))*6^n := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ (7*(n+6))*6^n := Nat.mul_le_mul_right _ (by omega)
      _ = 7*((n+6)*6^n) := by ac_rfl
      _ ≤ 7*(6*7^n) := Nat.mul_le_mul_left _ ih
      _ = 6*7^(n+1) := by rw [Nat.pow_succ]; ac_rfl

theorem six_power_multiple_lt_seven (L : Nat) :
    L*6^(6*L) < 7^(6*L) := by
  have h := bernoulli_seven_six (6*L)
  have hp : 0 < 6^(6*L) := Nat.pow_pos (by decide)
  simp only [Nat.add_mul,Nat.mul_assoc] at h
  omega

/-- A fixed translation-word boundary estimate is incompatible with all
levels of a hierarchy growing by at least seven cells and at most six edges. -/
theorem no_uniform_area_boundary_bound (A B : Nat → Nat) (C L : Nat)
    (ha : ∀ n, 7^n ≤ A n) (hb : ∀ n, B n ≤ C*6^n)
    (hbound : ∀ n, A n ≤ L*B n) : False := by
  let n := 6*(L*C)
  have hl : (L*C)*6^n < 7^n := six_power_multiple_lt_seven (L*C)
  have hu : A n ≤ (L*C)*6^n := by
    calc
      A n ≤ L*B n := hbound n
      _ ≤ L*(C*6^n) := Nat.mul_le_mul_left L (hb n)
      _ = (L*C)*6^n := by rw [Nat.mul_assoc]
  have hh := ha n
  omega

end SpectreFinite.AreaBoundaryGrowth
