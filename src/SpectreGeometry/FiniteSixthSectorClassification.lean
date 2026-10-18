module

-- These two compatibility imports exactly bind the preserved accepted
-- SixthSectorBalance historical input inventory. Current parsed closure
-- otherwise differed only by these entries, with zero shared hash conflicts.
-- They preserve strict dependency-snapshot validation without relaxing it.
public import Mathlib.Data.Sym.Sym2.Init
public import Batteries.Classes.Cast
public import SpectreGeometry.SixthSectorBalance

@[expose] public section


/-! Finite actual-sector classification can be assembled without supplying an
ordinary angular total: that integer is summed from the individual sectors.
The full-turn equality remains an input here and is proved by the cone fan. -/
namespace SpectreGeometry
noncomputable section
open scoped BigOperators

theorem finite_sixth_sector_classification {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (K : ι → Prop)
    (hroot : ∃ i, K i ∧ θ i ≠ Real.pi)
    (hkey : ∀ i, K i → 11*Real.pi/12 < θ i ∧ θ i < 13*Real.pi/12)
    (hordinary : ∀ i, ¬ K i → ∃ k : ℕ, 0 < k ∧ θ i = (k : ℝ)*(Real.pi/6))
    (hsum : ∑ i, θ i = 2*Real.pi) :
    Fintype.card ι = 2 ∧ ∀ i, K i := by
  classical
  let S := Finset.univ.filter K
  let O := Finset.univ.filter (fun i => ¬ K i)
  have hex : ∀ i, ∃ k : ℕ, ¬ K i → 0 < k ∧ θ i = (k : ℝ)*(Real.pi/6) := by
    intro i
    by_cases hi : K i
    · exact ⟨0,fun h => (h hi).elim⟩
    · obtain ⟨k,hk,he⟩ := hordinary i hi
      exact ⟨k,fun _ => ⟨hk,he⟩⟩
  choose k hk using hex
  let N : ℕ := ∑ i ∈ O, k i
  have hord : ∑ i ∈ O, θ i = (N : ℝ)*(Real.pi/6) := by
    dsimp [N]
    rw [Nat.cast_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hk i (Finset.mem_filter.mp hi).2).2
  have hbalance : (∑ i ∈ S, θ i) + N*(Real.pi/6) = 2*Real.pi := by
    rw [← hord]
    simpa only [S,O,Finset.sum_filter_add_sum_filter_not] using hsum
  have hb := sixth_sector_angle_balance_one_nonflat S θ N
    (by obtain ⟨i,hi,hne⟩ := hroot; exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩,hne⟩)
    (by intro i hi; exact hkey i (Finset.mem_filter.mp hi).2) hbalance
  have hall : ∀ i, K i := by
    intro i
    by_contra hi
    have hiO : i ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
    have hle : k i ≤ N := Finset.single_le_sum (fun j hj => Nat.zero_le _) hiO
    have hpos := (hk i hi).1
    omega
  refine ⟨?_,hall⟩
  have he : S = Finset.univ := by ext i; simp [S,hall]
  simpa only [he,Finset.card_univ] using hb.1

end
end SpectreGeometry
