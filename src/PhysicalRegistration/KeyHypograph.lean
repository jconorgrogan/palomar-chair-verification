module

public import PhysicalRegistration.KeyTent

@[expose] public section


/-!
An actual keyed facet as a subset of real inner-product space, and proved
local graph charts at all its graph points. This is the literal half-space
with one keyed graph, not yet the bounded chair assembled from many facets.
-/

namespace PhysicalRegistration
open scoped InnerProductSpace
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def graphHypograph (outward : E) (H : E → ℝ) : Set E :=
  {x | ⟪outward, x⟫_ℝ ≤ H x}

theorem graphHypograph_strict_mem_interior (n : E) (hn : ‖n‖ = 1)
    (H : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hH : ∀ x y, |H x - H y| ≤ L * ‖x - y‖)
    {x : E} (hx : ⟪n, x⟫_ℝ < H x) :
    x ∈ interior (graphHypograph n H) := by
  have hHlip : LipschitzWith ⟨L, hL⟩ H := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (H x) (H y) ≤ L * dist x y
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hH x y
  have hnLip : LipschitzWith 1 (fun x => ⟪n, x⟫_ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := affine_unit_axis_lipschitz n hn 1 0 1 (by norm_num) x y
    simpa [Real.dist_eq, dist_eq_norm] using h
  have hopen : IsOpen {x | ⟪n, x⟫_ℝ < H x} :=
    isOpen_lt hnLip.continuous hHlip.continuous
  apply interior_mono (s := {x | ⟪n, x⟫_ℝ < H x}) (t := graphHypograph n H)
      (fun y (h : ⟪n, y⟫_ℝ < H y) => (show y ∈ graphHypograph n H from h.le))
  rw [hopen.interior_eq]
  exact hx

/-- A global Lipschitz height that is constant in the carrier-normal direction
gives genuine local inward charts for its literal hypograph. -/
noncomputable def graphHypograph_local_graph (n : E) (hn : ‖n‖ = 1)
    (H : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hH : ∀ x y, |H x - H y| ≤ L * ‖x - y‖)
    (hshift : ∀ (x : E) (s : ℝ), H (x + s • n) = H x)
    (x : E) (hx : ⟪n, x⟫_ℝ = H x) :
    LocalLipschitzGraphAt (graphHypograph n H) x L where
  inward := -n
  inward_unit := by simpa using hn
  radius := 1
  radius_pos := by norm_num
  height := fun v => H x - H (x + v)
  height_zero := by simp
  height_lipschitz := by
    intro v w _ _ _ _
    have h := hH (x + w) (x + v)
    have hid : x + w - (x + v) = w - v := by abel
    rw [hid, norm_sub_rev] at h
    convert h using 1 <;> congr 1 <;> ring
  interior_above := by
    intro v s hv _ _ hs
    have hv' : ⟪n, v⟫_ℝ = 0 := by simpa using hv
    have Hval : H (x + v + s • (-n)) = H (x + v) := by
      simpa only [smul_neg, neg_smul] using hshift (x + v) (-s)
    apply graphHypograph_strict_mem_interior n hn H L hL hH
    rw [Hval]
    have hinner : ⟪n, x + v + s • (-n)⟫_ℝ = H x - s := by
      rw [inner_add_right, inner_add_right, real_inner_smul_right,
        inner_neg_right, real_inner_self_eq_norm_sq, hn, hx, hv']
      ring
    rw [hinner]
    linarith

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem keyHeight_normal_shift (eta a N : ℝ) (pMinus pPlus : ι → ℝ)
    (axis : ι → E) (n : E) (horth : ∀ i, ⟪axis i, n⟫_ℝ = 0)
    (x : E) (s : ℝ) :
    keyHeight eta a N pMinus pPlus axis (x + s • n) =
      keyHeight eta a N pMinus pPlus axis x := by
  simp only [keyHeight, keyTentProfile, finiteLowerEnvelope, inner_add_right,
    real_inner_smul_right, horth, mul_zero, add_zero]

/-- The concrete max-min key has a proved local graph chart at every point
of its boundary graph, including its apex, base corners, and zero extension. -/
noncomputable def keyHeight_local_graph (eta a N J pMax : ℝ)
    (heta : 0 < eta) (hN : 0 < N) (ha : |a| ≤ J) (hMax : 0 ≤ pMax)
    (pMinus pPlus : ι → ℝ) (axis : ι → E)
    (hMinus : ∀ i, 0 ≤ pMinus i ∧ pMinus i ≤ pMax)
    (hPlus : ∀ i, 0 ≤ pPlus i ∧ pPlus i ≤ pMax)
    (haxis : ∀ i, ‖axis i‖ = 1)
    (n : E) (hn : ‖n‖ = 1) (horth : ∀ i, ⟪axis i, n⟫_ℝ = 0)
    (x : E) (hx : ⟪n, x⟫_ℝ = keyHeight eta a N pMinus pPlus axis x) :
    LocalLipschitzGraphAt
      (graphHypograph n (keyHeight eta a N pMinus pPlus axis)) x (J * pMax / N) :=
  graphHypograph_local_graph n hn (keyHeight eta a N pMinus pPlus axis) (J * pMax / N)
    (div_nonneg (mul_nonneg ((abs_nonneg a).trans ha) hMax) hN.le)
    (keyHeight_lipschitz eta a N J pMax heta hN ha hMax
      pMinus pPlus axis hMinus hPlus haxis)
    (keyHeight_normal_shift eta a N pMinus pPlus axis n horth) x hx

#print axioms graphHypograph_strict_mem_interior
#print axioms graphHypograph_local_graph
#print axioms keyHeight_normal_shift
#print axioms keyHeight_local_graph
end PhysicalRegistration
