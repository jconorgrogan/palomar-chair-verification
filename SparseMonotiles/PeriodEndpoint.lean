module

public import SparseMonotiles.Model
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace SparseMonotiles

/-- The arithmetic endpoint. This does not assert that a tiling has a hierarchy. -/
theorem int_eq_zero_of_all_dyadic_dvd (z : ℤ)
    (h : ∀ n : ℕ, (2 : ℤ)^n ∣ z) : z = 0 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt |z| (show (1 : ℤ) < 2 by norm_num)
  exact Int.eq_zero_of_abs_lt_dvd (h n) hn

theorem integer_vector_eq_zero_of_all_dyadic_dvd {d : ℕ} (v : Fin d → ℤ)
    (h : ∀ n : ℕ, ∀ i, (2 : ℤ)^n ∣ v i) : v = 0 := by
  funext i
  exact int_eq_zero_of_all_dyadic_dvd (v i) (fun n => h n i)

def InDyadicLattice {d : ℕ} (n : ℕ) (v : Point d) : Prop :=
  ∃ z : Fin d → ℤ, ∀ i, v i = (2 : ℝ)^n * (z i : ℝ)

theorem point_eq_zero_of_all_dyadic_lattices {d : ℕ} (v : Point d)
    (h : ∀ n : ℕ, InDyadicLattice n v) : v = 0 := by
  obtain ⟨z, hz⟩ := h 0
  have hv : ∀ i, v i = (z i : ℝ) := by
    intro i
    simpa using hz i
  have hdiv : ∀ n : ℕ, ∀ i, (2 : ℤ)^n ∣ z i := by
    intro n i
    obtain ⟨w, hw⟩ := h n
    refine ⟨w i, ?_⟩
    have hi : (z i : ℝ) = (2 : ℝ)^n * (w i : ℝ) := (hv i).symm.trans (hw i)
    exact_mod_cast hi
  have hz0 := integer_vector_eq_zero_of_all_dyadic_dvd z hdiv
  ext i
  rw [hv i]
  simp [hz0]

/-- Registration may choose a different global orthonormal coordinate frame. -/
theorem point_eq_zero_of_normalized_dyadic_lattices {d : ℕ} (v : Point d)
    (f : Point d → Point d) (hf : Function.Injective f) (h0 : f 0 = 0)
    (h : ∀ n : ℕ, InDyadicLattice n (f v)) : v = 0 := by
  apply hf
  rw [point_eq_zero_of_all_dyadic_lattices (f v) h, h0]

/-- Explicitly conditional bridge. Its premise is still open for T5 and T7. -/
theorem aperiodic_of_period_divisibility {d : ℕ} (T : Set (Point d))
    (h : ∀ tiles, IsTiling T tiles → ∀ v, IsPeriod tiles v →
      ∀ n, InDyadicLattice n v) : IsAperiodic T := by
  intro tiles ht v hp
  exact point_eq_zero_of_all_dyadic_lattices v (h tiles ht v hp)

#print axioms int_eq_zero_of_all_dyadic_dvd
#print axioms integer_vector_eq_zero_of_all_dyadic_dvd
#print axioms point_eq_zero_of_all_dyadic_lattices
#print axioms point_eq_zero_of_normalized_dyadic_lattices
#print axioms aperiodic_of_period_divisibility

end SparseMonotiles
