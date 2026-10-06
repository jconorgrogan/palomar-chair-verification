module

public import SparseMonotiles.Constants
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
Analytic bounds for the canonical side/base and perpendicular-side crease
deviations. Identifying these formulae with the actual body's complete ridge
inventory is a separate geometric obligation.
-/
namespace SparseMonotiles

noncomputable def baseCreaseDeviation (s : ℝ) : ℝ := Real.arctan s

noncomputable def sideCreaseDeviation (s t : ℝ) : ℝ :=
  Real.arccos (1 / Real.sqrt ((1 + s^2) * (1 + t^2)))

theorem baseCreaseDeviation_bounds (s : ℝ) (hs : 0 < s) (hmax : s ≤ 1/2) :
    0 < baseCreaseDeviation s ∧ baseCreaseDeviation s < Real.pi / 4 := by
  constructor
  · simpa [baseCreaseDeviation] using Real.arctan_strictMono hs
  · have h := Real.arctan_strictMono (show s < 1 by linarith)
    simpa [baseCreaseDeviation, Real.arctan_one] using h

theorem sideCreaseDeviation_bounds (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hsmax : s ≤ 1/2) (htmax : t ≤ 1/2) :
    0 < sideCreaseDeviation s t ∧ sideCreaseDeviation s t < Real.pi / 4 := by
  let p := (1 + s^2) * (1 + t^2)
  have hp1 : 1 < p := by
    dsimp [p]
    nlinarith [sq_pos_of_pos hs, sq_pos_of_pos ht,
      mul_nonneg (sq_nonneg s) (sq_nonneg t)]
  have hp2 : p < 2 := perpendicular_slopes_sector_bound s t hs.le ht.le hsmax htmax
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hroot0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hroot1 : 1 < Real.sqrt p := by
    simpa using Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) hp1
  have hroot2 : Real.sqrt p < Real.sqrt 2 := Real.sqrt_lt_sqrt hp0.le hp2
  have harg1 : 1 / Real.sqrt p < 1 := by
    exact (div_lt_one hroot0).mpr hroot1
  have hargcos : Real.cos (Real.pi / 4) < 1 / Real.sqrt p := by
    have hinv := one_div_lt_one_div_of_lt hroot0 hroot2
    have hcos : Real.cos (Real.pi / 4) = 1 / Real.sqrt 2 := by
      rw [Real.cos_pi_div_four]
      have hne : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp
      exact Real.sq_sqrt (by norm_num)
    rw [hcos]
    exact hinv
  constructor
  · exact Real.arccos_pos.mpr harg1
  · have h := Real.arccos_lt_arccos (Real.neg_one_le_cos (Real.pi / 4)) hargcos harg1.le
    rw [Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])] at h
    exact h

#print axioms baseCreaseDeviation_bounds
#print axioms sideCreaseDeviation_bounds

end SparseMonotiles
