module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
Constructive three-normal cone lemma for arbitrary real inner product spaces.
This file proves only vector algebra. In a physical registration argument,
one must separately provide genuine local one-sided graph neighborhoods,
with a common Lipschitz bound below 1/2, and local disjointness of interiors.
No tangent-cone or polyhedral regularity assumption is silently supplied here.
-/
namespace PhysicalRegistration
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Among three unit vectors, one pair has inner product at least -1/2. -/
theorem three_unit_pair (u v w : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    -(1 / 2 : ℝ) ≤ ⟪u, v⟫_ℝ ∨
    -(1 / 2 : ℝ) ≤ ⟪u, w⟫_ℝ ∨
    -(1 / 2 : ℝ) ≤ ⟪v, w⟫_ℝ := by
  have huv := norm_add_sq_real u v
  have huv_w := norm_add_sq_real (u + v) w
  rw [hu, hv] at huv
  rw [hw, inner_add_left] at huv_w
  by_cases h₁ : -(1 / 2 : ℝ) ≤ ⟪u, v⟫_ℝ
  · exact Or.inl h₁
  by_cases h₂ : -(1 / 2 : ℝ) ≤ ⟪u, w⟫_ℝ
  · exact Or.inr (Or.inl h₂)
  apply Or.inr
  apply Or.inr
  nlinarith [sq_nonneg ‖u + v + w‖]

/-- The sum of a pair meeting the -1/2 bound lies strictly in both inward
cones for every slope L < 1/2. In particular, that sum is nonzero. -/
theorem pair_inward_cones (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : -(1 / 2 : ℝ) ≤ ⟪u, v⟫_ℝ)
    (L : ℝ) (hL : L < 1 / 2) :
    ∃ z : E, z ≠ 0 ∧ L * ‖z‖ < ⟪u, z⟫_ℝ ∧ L * ‖z‖ < ⟪v, z⟫_ℝ := by
  have hs := norm_add_sq_real u v
  rw [hu, hv] at hs
  have hn : 1 ≤ ‖u + v‖ := by
    nlinarith [norm_nonneg (u + v)]
  have ht : 0 < ‖u + v‖ := by linarith
  have hprod : 0 ≤ (‖u + v‖ - 1) * ‖u + v‖ :=
    mul_nonneg (sub_nonneg.mpr hn) (norm_nonneg _)
  have hhalf : L * ‖u + v‖ < (1 / 2 : ℝ) * ‖u + v‖ :=
    mul_lt_mul_of_pos_right hL ht
  have hu_dot : ⟪u, u + v⟫_ℝ = 1 + ⟪u, v⟫_ℝ := by
    rw [inner_add_right, real_inner_self_eq_norm_sq, hu]
    norm_num
  have hv_dot : ⟪v, u + v⟫_ℝ = 1 + ⟪u, v⟫_ℝ := by
    rw [inner_add_right, real_inner_self_eq_norm_sq, hv, real_inner_comm u v]
    simp [add_comm]
  refine ⟨u + v, ?_, ?_, ?_⟩
  · intro hz
    rw [hz, norm_zero] at hn
    norm_num at hn
  · nlinarith
  · nlinarith

/-- Three unit inward normals force two of the strict cones to meet.
The indices are distinct even when the vectors themselves coincide. -/
theorem three_unit_inward_cones (u : Fin 3 → E)
    (hu : ∀ i, ‖u i‖ = 1) (L : ℝ) (hL : L < 1 / 2) :
    ∃ (i j : Fin 3) (z : E), i ≠ j ∧ z ≠ 0 ∧
      L * ‖z‖ < ⟪u i, z⟫_ℝ ∧ L * ‖z‖ < ⟪u j, z⟫_ℝ := by
  rcases three_unit_pair (u 0) (u 1) (u 2) (hu 0) (hu 1) (hu 2) with h | h | h
  · obtain ⟨z, hz, hi, hj⟩ := pair_inward_cones (u 0) (u 1) (hu 0) (hu 1) h L hL
    exact ⟨0, 1, z, by decide, hz, hi, hj⟩
  · obtain ⟨z, hz, hi, hj⟩ := pair_inward_cones (u 0) (u 2) (hu 0) (hu 2) h L hL
    exact ⟨0, 2, z, by decide, hz, hi, hj⟩
  · obtain ⟨z, hz, hi, hj⟩ := pair_inward_cones (u 1) (u 2) (hu 1) (hu 2) h L hL
    exact ⟨1, 2, z, by decide, hz, hi, hj⟩

#print axioms three_unit_pair
#print axioms pair_inward_cones
#print axioms three_unit_inward_cones
end PhysicalRegistration
