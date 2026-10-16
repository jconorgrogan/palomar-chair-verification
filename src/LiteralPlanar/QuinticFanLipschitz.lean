module

public import LiteralPlanar.QuinticArc

@[expose] public section


/-! Quantitative scalar bounds for the literal polynomial fan displacement.
These are ordinary real inequalities. Actual Euclidean barycentric-coordinate
bounds, overlap pasting and whole-plane inversion remain separate steps. -/
namespace LiteralPlanar.Quintic
noncomputable section

private theorem abs_mul_le_one_of_bounds {a b : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]
  calc
    |a| * |b| ≤ 1 * 1 := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

private theorem product_difference_bound (a b c d : ℝ)
    (hb : |b| ≤ 1) (hc : |c| ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  have he : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [he]
  calc
    |(a - c) * b + c * (b - d)| ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * |b| + |c| * |b - d| := by rw [abs_mul, abs_mul]
    _ ≤ |a - c| * 1 + 1 * |b - d| :=
      add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = |a - c| + |b - d| := by ring

private theorem square_difference_bound (a c : ℝ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) : |a ^ 2 - c ^ 2| ≤ 2 * |a - c| := by
  simpa only [pow_two, two_mul] using product_difference_bound a a c c ha hc

/-- Uniform bound on the full parameter square, hence on every source simplex. -/
theorem fanHeight_difference_bound (ε α β α' β' : ℝ) (hε : 0 ≤ ε)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1)
    (hα' : 0 ≤ α' ∧ α' ≤ 1) (hβ' : 0 ≤ β' ∧ β' ≤ 1) :
    |fanHeight ε α β - fanHeight ε α' β'| ≤
      (3 * ε / 2) * (|α - α'| + |β - β'|) := by
  have ha : |α| ≤ 1 := by simpa [abs_of_nonneg hα.1] using hα.2
  have hb : |β| ≤ 1 := by simpa [abs_of_nonneg hβ.1] using hβ.2
  have ha' : |α'| ≤ 1 := by simpa [abs_of_nonneg hα'.1] using hα'.2
  have hb' : |β'| ≤ 1 := by simpa [abs_of_nonneg hβ'.1] using hβ'.2
  have haa : |α ^ 2| ≤ 1 := by simpa [pow_two] using abs_mul_le_one_of_bounds ha ha
  have hbb : |β ^ 2| ≤ 1 := by simpa [pow_two] using abs_mul_le_one_of_bounds hb hb
  have haa' : |α' ^ 2| ≤ 1 := by simpa [pow_two] using abs_mul_le_one_of_bounds ha' ha'
  have hsub : |β' - α'| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod : |(β' - α') * α' ^ 2| ≤ 1 := abs_mul_le_one_of_bounds hsub haa'
  have hdiff : |(β - α) - (β' - α')| ≤ |β - β'| + |α - α'| := by
    have he : (β - α) - (β' - α') = (β - β') - (α - α') := by ring
    rw [he]
    exact abs_sub _ _
  have hinner := product_difference_bound (β - α) (α ^ 2) (β' - α') (α' ^ 2) haa hsub
  have houter := product_difference_bound ((β - α) * α ^ 2) (β ^ 2)
    ((β' - α') * α' ^ 2) (β' ^ 2) hbb hprod
  have hsqa := square_difference_bound α α' ha ha'
  have hsqb := square_difference_bound β β' hb hb'
  have hbase : |(β - α) * α ^ 2 * β ^ 2 - (β' - α') * α' ^ 2 * β' ^ 2| ≤
      3 * (|α - α'| + |β - β'|) := by linarith
  have he : fanHeight ε α β - fanHeight ε α' β' =
      (ε / 2) * ((β - α) * α ^ 2 * β ^ 2 - (β' - α') * α' ^ 2 * β' ^ 2) := by
    unfold fanHeight
    ring
  rw [he, abs_mul, abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
  calc
    ε / 2 * |(β - α) * α ^ 2 * β ^ 2 - (β' - α') * α' ^ 2 * β' ^ 2| ≤
        ε / 2 * (3 * (|α - α'| + |β - β'|)) :=
      mul_le_mul_of_nonneg_left hbase (by linarith)
    _ = (3 * ε / 2) * (|α - α'| + |β - β'|) := by ring

/-- The exact numerical interface required from the Euclidean barycentric maps. -/
theorem fanHeight_difference_bound_of_parameter_bounds
    (ε α β α' β' r : ℝ) (hε : 0 ≤ ε)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1)
    (hα' : 0 ≤ α' ∧ α' ≤ 1) (hβ' : 0 ≤ β' ∧ β' ≤ 1)
    (hda : |α - α'| ≤ 30 * r) (hdb : |β - β'| ≤ 30 * r) :
    |fanHeight ε α β - fanHeight ε α' β'| ≤ 90 * ε * r := by
  calc
    _ ≤ (3 * ε / 2) * (|α - α'| + |β - β'|) :=
      fanHeight_difference_bound ε α β α' β' hε hα hβ hα' hβ'
    _ ≤ (3 * ε / 2) * (30 * r + 30 * r) :=
      mul_le_mul_of_nonneg_left (add_le_add hda hdb) (by linarith)
    _ = 90 * ε * r := by ring

theorem amplitude_residual_lt_eighth : 90 * amplitude < (1 / 8 : ℝ) := by
  norm_num [amplitude]

end
end LiteralPlanar.Quintic
