module

public import PhysicalRegistration.NativeDihedralAngles

@[expose] public section

/-!
# Finite arithmetic forcing exactly two complementary key sectors

This is the manuscript's final angle-count calculation, isolated from its
geometric premises. The sum identity is an explicit hypothesis here; deriving
it from actual covered planar germs is a separate measure/conservation proof.
No contact or whole-key conclusion is encoded in the input.
-/

namespace PhysicalRegistration
noncomputable section

/-- In quarter-turn units the total is four. Key sectors have weight strictly
between 3/2 and 5/2 and are not flat (weight two); ordinary sector weights sum
to the nonnegative integer N. These numerical facts force exactly two keys
and zero ordinary total. -/
theorem normalized_sector_balance {ι : Type*} (S : Finset ι) (w : ι → ℝ) (N : ℕ)
    (hne : S.Nonempty) (hw : ∀ i ∈ S, 3 / 2 < w i ∧ w i < 5 / 2 ∧ w i ≠ 2)
    (hsum : (∑ i ∈ S, w i) + N = 4) : S.card = 2 ∧ N = 0 := by
  have hstrict : (S.card : ℝ) * (3 / 2) < ∑ i ∈ S, w i := by
    calc
      (S.card : ℝ) * (3 / 2) = ∑ _i ∈ S, (3 / 2 : ℝ) := by simp
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
    have hn1 : (1 : ℝ) < N := by linarith [hi.2.1]
    have hn3 : (N : ℝ) < 3 := by linarith [hi.1]
    have hNi : N = 2 := by
      have h1' : 1 < N := by exact_mod_cast hn1
      have h3' : N < 3 := by exact_mod_cast hn3
      omega
    subst N
    norm_num at hsum
    exact (hi.2.2 (by linarith)).elim
  · refine ⟨h2, ?_⟩
    rw [h2] at hstrict
    norm_num at hstrict
    have hNlt : (N : ℝ) < 1 := by linarith
    have : N < 1 := by exact_mod_cast hNlt
    omega

/-- The same statement in radians: each actual key material angle differs
nontrivially from pi by less than pi/4, and all ordinary angles total N*pi/2. -/
theorem sector_angle_balance {ι : Type*} (S : Finset ι) (θ : ι → ℝ) (N : ℕ)
    (hne : S.Nonempty)
    (hθ : ∀ i ∈ S, 3 * Real.pi / 4 < θ i ∧ θ i < 5 * Real.pi / 4 ∧ θ i ≠ Real.pi)
    (hsum : (∑ i ∈ S, θ i) + N * (Real.pi / 2) = 2 * Real.pi) :
    S.card = 2 ∧ N = 0 := by
  have hp : 0 < Real.pi / 2 := by positivity
  apply normalized_sector_balance S (fun i => θ i / (Real.pi / 2)) N hne
  · intro i hi
    have h := hθ i hi
    refine ⟨(lt_div_iff₀ hp).mpr (by nlinarith [h.1]),
      (div_lt_iff₀ hp).mpr (by nlinarith [h.2.1]), ?_⟩
    intro he
    apply h.2.2
    have hh := (div_eq_iff hp.ne').mp he
    nlinarith
  · rw [← Finset.sum_div]
    field_simp
    nlinarith

#print axioms normalized_sector_balance
#print axioms sector_angle_balance
end
end PhysicalRegistration
