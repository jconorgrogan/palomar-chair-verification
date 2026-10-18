module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! Arithmetic for a carrier with ordinary sector angles in multiples of π/6.
The angle bounds and conservation identity remain explicit premises. This file
does not identify actual boundary cones, contacts, or a four-dimensional tiling. -/
namespace SpectreGeometry
noncomputable section

/-- In π/6 units, one nonflat key and the strict half-unit bounds force two
keys and no ordinary sector mass. -/
theorem normalized_sixth_sector_balance_one_nonflat {ι : Type*}
    (S : Finset ι) (w : ι → ℝ) (N : ℕ)
    (hroot : ∃ i ∈ S, w i ≠ 6)
    (hw : ∀ i ∈ S, 11 / 2 < w i ∧ w i < 13 / 2)
    (hsum : (∑ i ∈ S, w i) + N = 12) : S.card = 2 ∧ N = 0 := by
  have hne : S.Nonempty := by obtain ⟨i, hi, _⟩ := hroot; exact ⟨i, hi⟩
  have hstrict : (S.card : ℝ) * (11 / 2) < ∑ i ∈ S, w i := by
    calc
      (S.card : ℝ) * (11 / 2) = ∑ _i ∈ S, (11 / 2 : ℝ) := by simp
      _ < ∑ i ∈ S, w i := Finset.sum_lt_sum_of_nonempty hne (fun i hi => (hw i hi).1)
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hcardlt : (S.card : ℝ) < 3 := by linarith
  have hcard : S.card ≤ 2 := by
    have : S.card < 3 := by exact_mod_cast hcardlt
    omega
  have hpos : 0 < S.card := Finset.card_pos.mpr hne
  have hcases : S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with h1 | h2
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    have hi := hw i (Finset.mem_singleton_self i)
    simp only [Finset.sum_singleton] at hsum
    have hn5 : (5 : ℝ) < N := by linarith [hi.2]
    have hn7 : (N : ℝ) < 7 := by linarith [hi.1]
    have hNi : N = 6 := by
      have h5' : 5 < N := by exact_mod_cast hn5
      have h7' : N < 7 := by exact_mod_cast hn7
      omega
    subst N
    norm_num at hsum
    obtain ⟨j, hj, hflat⟩ := hroot
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    exact (hflat (by linarith)).elim
  · refine ⟨h2, ?_⟩
    rw [h2] at hstrict
    norm_num at hstrict
    have hNlt : (N : ℝ) < 1 := by linarith
    have : N < 1 := by exact_mod_cast hNlt
    omega

/-- Radian form. The ordinary angular total is explicitly N·π/6; deriving
that equality and the key bounds from physical geometry is a separate task. -/
theorem sixth_sector_angle_balance_one_nonflat {ι : Type*}
    (S : Finset ι) (θ : ι → ℝ) (N : ℕ)
    (hroot : ∃ i ∈ S, θ i ≠ Real.pi)
    (hθ : ∀ i ∈ S, 11 * Real.pi / 12 < θ i ∧ θ i < 13 * Real.pi / 12)
    (hsum : (∑ i ∈ S, θ i) + N * (Real.pi / 6) = 2 * Real.pi) :
    S.card = 2 ∧ N = 0 := by
  have hp : 0 < Real.pi / 6 := by linarith [Real.pi_pos]
  apply normalized_sixth_sector_balance_one_nonflat S (fun i => θ i / (Real.pi / 6)) N
  · obtain ⟨i, hi, hne⟩ := hroot
    refine ⟨i, hi, ?_⟩
    intro he
    apply hne
    have hh := (div_eq_iff hp.ne').mp he
    nlinarith
  · intro i hi
    have hh := hθ i hi
    exact ⟨(lt_div_iff₀ hp).mpr (by nlinarith [hh.1]),
      (div_lt_iff₀ hp).mpr (by nlinarith [hh.2])⟩
  · rw [← Finset.sum_div]
    field_simp
    nlinarith

end
end SpectreGeometry
