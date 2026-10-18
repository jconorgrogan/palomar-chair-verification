module

public import ProductClosure.PlacedConicalGerms

@[expose] public section

/-! A literal finite sign cone is locally constant off its nonzero normal
hyperplanes. This promotes actual cone membership to ambient interior
membership, as needed for angular overlap control. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace Topology
open Set PhysicalRegistration Filter
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}

/-- Away from the listed nonzero normal hyperplanes, membership in a finite
sign-defined cone is constant on an actual ambient neighborhood. -/
theorem SignDetermined.eventually_mem_iff  {N : Finset (Space m)}
    {C : Set (Space m)} (hC : SignDetermined N C) (z : Space m)
    (hz : ∀ n ∈ N, n ≠ 0 → ⟪n, z⟫_ℝ ≠ 0) :
    ∀ᶠ w in 𝓝 z, (w ∈ C ↔ z ∈ C) := by
  have hn (n : N) : ∀ᶠ w in 𝓝 z,
      (⟪(n : Space m), w⟫_ℝ ≤ 0 ↔ ⟪(n : Space m), z⟫_ℝ ≤ 0) ∧
      (0 ≤ ⟪(n : Space m), w⟫_ℝ ↔ 0 ≤ ⟪(n : Space m), z⟫_ℝ) := by
    by_cases hn0 : (n : Space m) = 0
    · simp [hn0]
    have hne := hz n n.property hn0
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hh : ∀ᶠ w in 𝓝 z, ⟪(n : Space m), w⟫_ℝ < 0 :=
        (isOpen_lt (continuous_const.inner continuous_id) continuous_const).mem_nhds hneg
      filter_upwards [hh] with w hw
      exact ⟨iff_of_true (le_of_lt hw) (le_of_lt hneg),
        iff_of_false (not_le_of_gt hw) (not_le_of_gt hneg)⟩
    · have hh : ∀ᶠ w in 𝓝 z, 0 < ⟪(n : Space m), w⟫_ℝ :=
        (isOpen_lt continuous_const (continuous_const.inner continuous_id)).mem_nhds hpos
      filter_upwards [hh] with w hw
      exact ⟨iff_of_false (not_le_of_gt hw) (not_le_of_gt hpos),
        iff_of_true (le_of_lt hw) (le_of_lt hpos)⟩
  have hall : ∀ᶠ w in 𝓝 z, ∀ n : N,
      (⟪(n : Space m), w⟫_ℝ ≤ 0 ↔ ⟪(n : Space m), z⟫_ℝ ≤ 0) ∧
      (0 ≤ ⟪(n : Space m), w⟫_ℝ ↔ 0 ≤ ⟪(n : Space m), z⟫_ℝ) :=
    eventually_all.mpr hn
  filter_upwards [hall] with w hw
  exact hC w z (fun n hn => hw ⟨n, hn⟩)

/-- Actual membership off the finite hyperplane arrangement is interior
membership in the full ambient space. -/
theorem SignDetermined.mem_interior_of_off_normals  {N : Finset (Space m)}
    {C : Set (Space m)} (hC : SignDetermined N C) {z : Space m}
    (hzC : z ∈ C) (hz : ∀ n ∈ N, n ≠ 0 → ⟪n, z⟫_ℝ ≠ 0) :
    z ∈ interior C := by
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [hC.eventually_mem_iff z hz] with w hw
  exact hw.mpr hzC

end
end ProductClosure.NativeCompiler
