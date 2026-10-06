module

public import SparseMonotiles.SectorAngleSumPlaneGeometry
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-! # Regularity of the genuine planar sector models
Every classified sector is the closure of its own interior. A positive-width
sector has nonempty interior; in particular no physical incident index needs
to be silently discarded from an angle partition.
-/
namespace SparseMonotiles.SectorAngleSum
open Set InnerProductGeometry
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem convex_normalHalfspace (n : E) : Convex ℝ (normalHalfspace n) := by
  intro x hx y hy a b ha hb _
  change 0 ≤ inner (𝕜 := ℝ) n (a • x + b • y)
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

private theorem isClosed_normalHalfspace (n : E) : IsClosed (normalHalfspace n) :=
  isClosed_le continuous_const (continuous_const.inner continuous_id)

private theorem strict_inner_mem_interior {n x : E} (hx : 0 < inner (𝕜 := ℝ) n x) :
    x ∈ interior (normalHalfspace n) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hopen : IsOpen {y : E | (0 : ℝ) < inner (𝕜 := ℝ) n y} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  apply Filter.mem_of_superset (hopen.mem_nhds hx)
  intro y hy
  change 0 ≤ inner (𝕜 := ℝ) n y
  exact le_of_lt hy

private theorem halfspace_interior_nonempty (n : E) (hn : n ≠ 0) :
    (interior (normalHalfspace n)).Nonempty :=
  ⟨n, strict_inner_mem_interior (real_inner_self_pos.mpr hn)⟩

private theorem two_halfspaces_interior_nonempty (n m : E) (hn : n ≠ 0) (hm : m ≠ 0)
    (ha : angle n m < Real.pi) :
    (interior (normalHalfspace n ∩ normalHalfspace m)).Nonempty := by
  have hn0 : 0 < ‖n‖ := norm_pos_iff.mpr hn
  have hm0 : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hcos : -1 < Real.cos (angle n m) := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (angle_nonneg n m) le_rfl ha
  have hinner : -(‖n‖ * ‖m‖) < inner (𝕜 := ℝ) n m := by
    have h := mul_lt_mul_of_pos_right hcos (mul_pos hn0 hm0)
    rw [cos_angle_mul_norm_mul_norm] at h
    simpa only [neg_one_mul] using h
  let w := ‖m‖ • n + ‖n‖ • m
  have hnw : 0 < inner (𝕜 := ℝ) n w := by
    have hh : 0 < ‖n‖ * (‖n‖ * ‖m‖ + inner (𝕜 := ℝ) n m) :=
      mul_pos hn0 (by linarith)
    simpa only [w, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] using
      (show 0 < ‖m‖ * ‖n‖^2 + ‖n‖ * inner (𝕜 := ℝ) n m by nlinarith [hh])
  have hmw : 0 < inner (𝕜 := ℝ) m w := by
    have hh : 0 < ‖m‖ * (‖n‖ * ‖m‖ + inner (𝕜 := ℝ) n m) :=
      mul_pos hm0 (by linarith)
    simpa only [w, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm m n] using
      (show 0 < ‖m‖ * inner (𝕜 := ℝ) n m + ‖n‖ * ‖m‖^2 by nlinarith [hh])
  refine ⟨w, ?_⟩
  rw [interior_inter]
  exact ⟨strict_inner_mem_interior hnw, strict_inner_mem_interior hmw⟩

private theorem halfspace_regular_closed (n : E) (hn : n ≠ 0) :
    closure (interior (normalHalfspace n)) = normalHalfspace n := by
  rw [(convex_normalHalfspace n).closure_interior_eq_closure_of_nonempty_interior
    (halfspace_interior_nonempty n hn), (isClosed_normalHalfspace n).closure_eq]

/-- Every genuine sector model, including the empty/full cases, is regular closed. -/
theorem HasSectorAngle.regular_closed {S : Set E} {θ : ℝ} (h : HasSectorAngle S θ) :
    closure (interior S) = S := by
  cases h with
  | empty hS => subst S; simp
  | full hS => subst S; simp
  | halfplane n hn hS => subst S; exact halfspace_regular_closed n hn
  | convex n m hn hm ha hS =>
      subst S
      rw [((convex_normalHalfspace n).inter (convex_normalHalfspace m)).closure_interior_eq_closure_of_nonempty_interior
        (two_halfspaces_interior_nonempty n m hn hm ha)]
      exact ((isClosed_normalHalfspace n).inter (isClosed_normalHalfspace m)).closure_eq
  | reflex n m hn hm _ hS =>
      subst S
      apply Subset.antisymm
      · exact closure_minimal interior_subset
          ((isClosed_normalHalfspace n).union (isClosed_normalHalfspace m))
      · intro x hx
        rcases hx with hx | hx
        · have hsub := closure_mono (interior_mono
            (show normalHalfspace n ⊆ normalHalfspace n ∪ normalHalfspace m from subset_union_left))
          exact hsub ((halfspace_regular_closed n hn).symm ▸ hx)
        · have hsub := closure_mono (interior_mono
            (show normalHalfspace m ⊆ normalHalfspace n ∪ normalHalfspace m from subset_union_right))
          exact hsub ((halfspace_regular_closed m hm).symm ▸ hx)

/-- A positive-width genuine sector has nonempty intrinsic interior. -/
theorem HasSectorAngle.interior_nonempty {S : Set E} {θ : ℝ}
    (h : HasSectorAngle S θ) (hθ : 0 < θ) : (interior S).Nonempty := by
  cases h with
  | empty hS => exact (lt_irrefl 0 hθ).elim
  | full hS => subst S; simp
  | halfplane n hn hS => subst S; exact halfspace_interior_nonempty n hn
  | convex n m hn hm ha hS => subst S; exact two_halfspaces_interior_nonempty n m hn hm ha
  | reflex n m hn _ _ hS =>
      subst S
      exact (halfspace_interior_nonempty n hn).mono (interior_mono subset_union_left)

#print axioms HasSectorAngle.regular_closed
#print axioms HasSectorAngle.interior_nonempty
end SparseMonotiles.SectorAngleSum
