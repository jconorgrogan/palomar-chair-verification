module

public import SpectreGeometry.CompactTilingIncidence
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section


/-! A uniform Lipschitz estimate on a locally finite closed cover glues to
a global estimate on a normed real vector space. The local-star argument
avoids any unproved finite segment-subdivision premise. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set
open scoped NNReal

private theorem interval_dist_le {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) (K : ℝ) (hf : Continuous f)
    (hlocal : ∀ x, ∃ r > 0, ∀ y, dist y x < r → dist (f y) (f x) ≤ K * dist y x)
    (a b : ℝ) (hab : a ≤ b) : dist (f b) (f a) ≤ K * (b-a) := by
  let S : Set ℝ := {t | dist (f t) (f a) ≤ K * (t-a)}
  have hc : IsClosed S := isClosed_le (hf.dist continuous_const)
    (continuous_const.mul (continuous_id.sub continuous_const))
  apply (hc.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt
    (s := S) (a := a) (b := b) (by simp [S]) hab
  intro t ht
  obtain ⟨r,hr,hbound⟩ := hlocal t
  let δ := min (r/2) ((b-t)/2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith [ht.2.2])
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδb : t+δ ≤ b := by have := min_le_right (r/2) ((b-t)/2); dsimp [δ]; linarith [ht.2.2]
  refine ⟨t+δ,?_,by dsimp [δ] at *; exact ⟨by linarith, hδb⟩⟩
  have hdist : dist (t+δ) t = δ := by rw [Real.dist_eq,add_sub_cancel_left,abs_of_pos hδ]
  have hh := hbound (t+δ) (by rwa [hdist])
  change dist (f (t+δ)) (f a) ≤ K * (t+δ-a)
  have ht' : dist (f t) (f a) ≤ K * (t-a) := ht.1
  rw [hdist] at hh
  calc
    dist (f (t+δ)) (f a) ≤ dist (f (t+δ)) (f t) + dist (f t) (f a) := dist_triangle _ _ _
    _ ≤ K*δ + K*(t-a) := add_le_add hh ht'
    _ = K*(t+δ-a) := by ring

/-- Uniform point-anchored local bounds imply a global Lipschitz bound.
No differentiability, local injectivity, or properness assumption is needed. -/
theorem lipschitz_of_local_anchor {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace Y] (g : E → Y) (q : ℝ≥0)
    (hlocal : ∀ x, ∃ r > 0, ∀ y, dist y x < r → dist (g y) (g x) ≤ q * dist y x) :
    LipschitzWith q g := by
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun x => by
    obtain ⟨r,hr,hh⟩ := hlocal x
    exact continuousAt_of_locally_lipschitz hr q hh
  apply LipschitzWith.of_dist_le_mul
  intro y x
  let p : ℝ → E := fun t => x+t • (y-x)
  have hp : Continuous p := by unfold p; fun_prop
  have hdist (s t : ℝ) : dist (p s) (p t) = |s-t| * dist y x := by
    rw [dist_eq_norm,dist_eq_norm]
    have he : p s - p t = (s-t) • (y-x) := by simp [p,sub_smul]
    rw [he,norm_smul,Real.norm_eq_abs]
  have hl : ∀ t, ∃ r > 0, ∀ s, dist s t < r →
      dist (g (p s)) (g (p t)) ≤ (q * dist y x) * dist s t := by
    intro t
    obtain ⟨r,hr,hh⟩ := hlocal (p t)
    obtain ⟨δ,hδ,hδ'⟩ := Metric.continuousAt_iff.mp hp.continuousAt r hr
    refine ⟨δ,hδ,fun s hs => ?_⟩
    have hb := hh (p s) (hδ' hs)
    rw [hdist,←Real.dist_eq] at hb
    simpa only [mul_assoc,mul_comm (dist s t),←mul_assoc] using hb
  have h := interval_dist_le (g ∘ p) (q * dist y x) (hg.comp hp) hl 0 1 (by norm_num)
  simpa [p] using h

/-- A common Lipschitz constant on a locally finite closed cover is global.
The map itself must already agree on overlaps; tilewise construction is separate. -/
theorem lipschitz_of_locallyFinite_closed_cover {E Y ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    (C : ι → Set E) (hlocal : LocallyFinite C) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ x, ∃ i, x ∈ C i) (g : E → Y) (q : ℝ≥0)
    (hpiece : ∀ i, LipschitzOnWith q g (C i)) : LipschitzWith q g := by
  apply lipschitz_of_local_anchor
  intro x
  obtain ⟨r,hr,hstar⟩ := CompactTilingIncidence.local_star_radius C hlocal hclosed x
  refine ⟨r,hr,fun y hy => ?_⟩
  obtain ⟨i,hi⟩ := hcover y
  exact (hpiece i).dist_le_mul y hi x (hstar i y hy hi)

end
end SpectreGeometry.Deformation
