module

public import PhysicalRegistration.SectorAngleBalance

@[expose] public section

/-! One genuinely nonflat root key suffices for the angle count. Other key
incidences may initially be flat side points; the balance itself rules these
out after finding the complementary pair. -/
namespace PhysicalRegistration
noncomputable section

theorem normalized_sector_balance_one_nonflat {ι : Type*} (S : Finset ι) (w : ι → ℝ) (N : ℕ)
    (hroot : ∃ i ∈ S, w i ≠ 2) (hw : ∀ i ∈ S, 3 / 2 < w i ∧ w i < 5 / 2)
    (hsum : (∑ i ∈ S, w i) + N = 4) : S.card = 2 ∧ N = 0 := by
  have hne : S.Nonempty := by obtain ⟨i, hi, _⟩ := hroot; exact ⟨i, hi⟩
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
    have hn1 : (1 : ℝ) < N := by linarith [hi.2]
    have hn3 : (N : ℝ) < 3 := by linarith [hi.1]
    have hNi : N = 2 := by
      have h1' : 1 < N := by exact_mod_cast hn1
      have h3' : N < 3 := by exact_mod_cast hn3
      omega
    subst N
    norm_num at hsum
    obtain ⟨j, hj, hne⟩ := hroot
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    exact (hne (by linarith)).elim
  · refine ⟨h2, ?_⟩
    rw [h2] at hstrict
    norm_num at hstrict
    have hNlt : (N : ℝ) < 1 := by linarith
    have : N < 1 := by exact_mod_cast hNlt
    omega

theorem sector_angle_balance_one_nonflat {ι : Type*} (S : Finset ι) (θ : ι → ℝ) (N : ℕ)
    (hroot : ∃ i ∈ S, θ i ≠ Real.pi)
    (hθ : ∀ i ∈ S, 3 * Real.pi / 4 < θ i ∧ θ i < 5 * Real.pi / 4)
    (hsum : (∑ i ∈ S, θ i) + N * (Real.pi / 2) = 2 * Real.pi) :
    S.card = 2 ∧ N = 0 := by
  have hp : 0 < Real.pi / 2 := by positivity
  apply normalized_sector_balance_one_nonflat S (fun i => θ i / (Real.pi / 2)) N
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

/-- When two sectors sum to a full turn, nonflatness of either forces
nonflatness of both. -/
theorem complementary_pair_nonflat {ι : Type*} (S : Finset ι) (θ : ι → ℝ)
    (hcard : S.card = 2) (hsum : ∑ i ∈ S, θ i = 2 * Real.pi)
    (hroot : ∃ i ∈ S, θ i ≠ Real.pi) : ∀ i ∈ S, θ i ≠ Real.pi := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  rw [Finset.sum_pair hab] at hsum
  have hboth : θ a ≠ Real.pi ∧ θ b ≠ Real.pi := by
    constructor <;> intro he
    · have hb : θ b = Real.pi := by linarith
      obtain ⟨i, hi, hne⟩ := hroot
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> contradiction
    · have ha : θ a = Real.pi := by linarith
      obtain ⟨i, hi, hne⟩ := hroot
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> contradiction
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact hboth.1
  · exact hboth.2

#print axioms normalized_sector_balance_one_nonflat
#print axioms sector_angle_balance_one_nonflat
#print axioms complementary_pair_nonflat
end
end PhysicalRegistration
