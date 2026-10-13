module

public import PhysicalRegistration.ThreeCones

@[expose] public section

/-!
Actual local Lipschitz graph neighborhoods for the registration bridge.
The local inclusion below is about the interior of a set, not an abstract
tangent cone. No concrete keyed polyhedron is constructed in this file.
-/

namespace PhysicalRegistration
open scoped InnerProductSpace
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine inward local graph chart. Only the tangent ball is constrained;
the height function's values off that ball are immaterial. -/
structure LocalLipschitzGraphAt (S : Set E) (x : E) (L : ℝ) where
  inward : E
  inward_unit : ‖inward‖ = 1
  radius : ℝ
  radius_pos : 0 < radius
  height : E → ℝ
  height_zero : height 0 = 0
  height_lipschitz : ∀ v w : E,
    ⟪inward, v⟫_ℝ = 0 → ⟪inward, w⟫_ℝ = 0 →
    ‖v‖ < radius → ‖w‖ < radius →
    |height v - height w| ≤ L * ‖v - w‖
  interior_above : ∀ (v : E) (s : ℝ),
    ⟪inward, v⟫_ℝ = 0 → ‖v‖ < radius → |s| < radius →
    height v < s → x + v + s • inward ∈ interior S

theorem LocalLipschitzGraphAt.height_le {S : Set E} {x : E} {L : ℝ}
    (G : LocalLipschitzGraphAt S x L) {v : E}
    (hv : ⟪G.inward, v⟫_ℝ = 0) (hvr : ‖v‖ < G.radius) :
    G.height v ≤ L * ‖v‖ := by
  have h := G.height_lipschitz v 0 hv (by simp) hvr (by simpa using G.radius_pos)
  simp only [G.height_zero, sub_zero] at h
  exact (le_abs_self _).trans h

/-- A strict inward direction enters the actual interior at every sufficiently
small positive scalar, using the local graph chart. -/
theorem LocalLipschitzGraphAt.interior_of_strict_inward
    {S : Set E} {x : E} {L : ℝ} (G : LocalLipschitzGraphAt S x L)
    (hL : 0 ≤ L) {z : E} (hz : L * ‖z‖ < ⟪G.inward, z⟫_ℝ)
    {t : ℝ} (ht : 0 < t) (htr : t * ‖z‖ < G.radius) :
    x + t • z ∈ interior S := by
  let s : ℝ := ⟪G.inward, z⟫_ℝ
  let v : E := z - s • G.inward
  have huv : ⟪G.inward, v⟫_ℝ = 0 := by
    dsimp [v, s]
    rw [inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, G.inward_unit]
    simp
  have hdecomp : v + s • G.inward = z := by
    dsimp [v]
    exact sub_add_cancel _ _
  have hvnorm : ‖v‖ ≤ ‖z‖ := by
    have horth : ⟪v, s • G.inward⟫_ℝ = 0 := by
      rw [real_inner_smul_right, real_inner_comm G.inward v, huv, mul_zero]
    have hsq := norm_add_sq_real v (s • G.inward)
    rw [hdecomp, horth] at hsq
    nlinarith [sq_nonneg ‖s • G.inward‖, norm_nonneg v, norm_nonneg z]
  have hsabs : |s| ≤ ‖z‖ := by
    simpa [s, G.inward_unit] using abs_real_inner_le_norm G.inward z
  have htabs : |t| = t := abs_of_pos ht
  have htv : ⟪G.inward, t • v⟫_ℝ = 0 := by
    rw [real_inner_smul_right, huv, mul_zero]
  have htvnorm : ‖t • v‖ < G.radius := by
    rw [norm_smul, Real.norm_eq_abs, htabs]
    exact (mul_le_mul_of_nonneg_left hvnorm ht.le).trans_lt htr
  have htsabs : |t * s| < G.radius := by
    rw [abs_mul, htabs]
    exact (mul_le_mul_of_nonneg_left hsabs ht.le).trans_lt htr
  have hdir : L * ‖v‖ < s :=
    (mul_le_mul_of_nonneg_left hvnorm hL).trans_lt hz
  have hheight : G.height (t • v) < t * s := by
    have hh := G.height_le htv htvnorm
    rw [norm_smul, Real.norm_eq_abs, htabs] at hh
    have hscaled := mul_lt_mul_of_pos_left hdir ht
    nlinarith
  have hpoint := G.interior_above (t • v) (t * s) htv htvnorm htsabs hheight
  rwa [add_assoc, mul_smul, ← smul_add, hdecomp] at hpoint

/-- Three interior-disjoint sets cannot all have shallow local key-graph
charts at the same point. This is an actual-neighborhood theorem. -/
theorem no_three_local_graphs (S : Fin 3 → Set E) (x : E) (L : ℝ)
    (hL0 : 0 ≤ L) (hL : L < 1 / 2)
    (G : ∀ i, LocalLipschitzGraphAt (S i) x L)
    (hdisjoint : Pairwise fun i j => Disjoint (interior (S i)) (interior (S j))) :
    False := by
  obtain ⟨i, j, z, hij, _, hzi, hzj⟩ :=
    three_unit_inward_cones (fun i => (G i).inward)
      (fun i => (G i).inward_unit) L hL
  let r := min (G i).radius (G j).radius
  have hr : 0 < r := lt_min (G i).radius_pos (G j).radius_pos
  let t := r / (2 * (1 + ‖z‖))
  have hden : 0 < 2 * (1 + ‖z‖) := by positivity
  have ht : 0 < t := div_pos hr hden
  have htr : t * ‖z‖ < r := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le (norm_nonneg z)]
  have hi := (G i).interior_of_strict_inward hL0 hzi ht
    (htr.trans_le (min_le_left _ _))
  have hj := (G j).interior_of_strict_inward hL0 hzj ht
    (htr.trans_le (min_le_right _ _))
  exact Set.disjoint_left.mp (hdisjoint hij) hi hj

#print axioms LocalLipschitzGraphAt.height_le
#print axioms LocalLipschitzGraphAt.interior_of_strict_inward
#print axioms no_three_local_graphs
end PhysicalRegistration
