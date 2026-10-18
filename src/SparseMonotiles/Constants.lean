module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace SparseMonotiles

def widths5 : Fin 4 → ℚ := ![1/80, 1/64, 3/160, 7/320]
def offsets5 : Fin 4 → ℚ := ![1/240, 1/256, 3/800, 7/1920]
def widths7 : Fin 6 → ℚ := ![1/112, 1/96, 1/84, 3/224, 5/336, 11/672]
def offsets7 : Fin 6 → ℚ := ![1/336, 1/384, 1/420, 1/448, 5/2352, 11/5376]

theorem key5_offsets_inside (i : Fin 4) :
    0 < offsets5 i ∧ offsets5 i < widths5 i := by
  fin_cases i <;> norm_num [offsets5, widths5]

theorem key7_offsets_inside (i : Fin 6) :
    0 < offsets7 i ∧ offsets7 i < widths7 i := by
  fin_cases i <;> norm_num [offsets7, widths7]

theorem key5_inside_collar (i : Fin 4) :
    ((i.val + 1 : ℕ) : ℚ) / 20 + widths5 i < 1/4 := by
  fin_cases i <;> norm_num [widths5]

theorem key7_inside_collar (i : Fin 6) :
    ((i.val + 1 : ℕ) : ℚ) / 28 + widths7 i < 1/4 := by
  fin_cases i <;> norm_num [widths7]

theorem key5_halfwidth_bound (i : Fin 4) : widths5 i ≤ 7/320 := by
  fin_cases i <;> norm_num [widths5]

theorem key7_halfwidth_bound (i : Fin 6) : widths7 i ≤ 11/672 := by
  fin_cases i <;> norm_num [widths7]

theorem key5_support_gap : (2 : ℚ) * (7/320) < 1/20 := by norm_num
theorem key7_support_gap : (2 : ℚ) * (11/672) < 1/28 := by norm_num

theorem key5_squared_diagonal_bound :
    (∑ i : Fin 4, (2 * widths5 i)^2) + (1/240 : ℚ)^2 < (1/4 : ℚ)^2 := by
  norm_num [Fin.sum_univ_succ, widths5]

theorem key7_squared_diagonal_bound :
    (∑ i : Fin 6, (2 * widths7 i)^2) + (1/336 : ℚ)^2 < (1/4 : ℚ)^2 := by
  norm_num [Fin.sum_univ_succ, widths7]

theorem key5_slope_bound (i : Fin 4) :
    (1/240 : ℚ) / (widths5 i - offsets5 i) ≤ 1/2 ∧
    (1/240 : ℚ) / (widths5 i + offsets5 i) ≤ 1/2 := by
  fin_cases i <;> norm_num [offsets5, widths5]

theorem key7_slope_bound (i : Fin 6) :
    (1/336 : ℚ) / (widths7 i - offsets7 i) ≤ 1/2 ∧
    (1/336 : ℚ) / (widths7 i + offsets7 i) ≤ 1/2 := by
  fin_cases i <;> norm_num [offsets7, widths7]

theorem tile5_clamp_bound : (Real.sqrt 5 + 1) * (1/240 : ℝ) < 1/2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  nlinarith

theorem tile7_clamp_bound : (Real.sqrt 7 + 1) * (1/336 : ℝ) < 1/2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)
  have hn := Real.sqrt_nonneg (7 : ℝ)
  nlinarith

/-- Algebraic normal-angle bound used before the arccos sector argument. -/
theorem perpendicular_slopes_sector_bound (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hs' : s ≤ 1/2) (ht' : t ≤ 1/2) :
    (1 + s^2) * (1 + t^2) < 2 := by
  have hs2 : s^2 ≤ 1/4 := by nlinarith
  have ht2 : t^2 ≤ 1/4 := by nlinarith
  have hp := mul_le_mul hs2 ht2 (sq_nonneg t) (by norm_num : (0 : ℝ) ≤ 1/4)
  nlinarith

#print axioms key5_offsets_inside
#print axioms key7_offsets_inside
#print axioms key5_inside_collar
#print axioms key7_inside_collar
#print axioms key5_halfwidth_bound
#print axioms key7_halfwidth_bound
#print axioms key5_support_gap
#print axioms key7_support_gap
#print axioms key5_squared_diagonal_bound
#print axioms key7_squared_diagonal_bound
#print axioms key5_slope_bound
#print axioms key7_slope_bound
#print axioms tile5_clamp_bound
#print axioms tile7_clamp_bound
#print axioms perpendicular_slopes_sector_bound

end SparseMonotiles
