module

public import SpectreGeometry.TriangleGeometry

@[expose] public section


/-! A supporting affine halfplane cuts a convex hull down to the convex
hull of its zero vertices. No finite-dimensional separation theorem is used. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem convexHull_nonpositive_zero_face (a b : RealPoint) (s face : Set RealPoint)
    (hs : ∀ x ∈ s, side a b x ≤ 0)
    (hf : ∀ x ∈ s, side a b x = 0 → x ∈ face)
    (x : RealPoint) (hx : x ∈ convexHull ℝ s) (hz : side a b x = 0) :
    x ∈ convexHull ℝ face := by
  let T : Set RealPoint := {y | side a b y ≤ 0 ∧ (side a b y = 0 → y ∈ convexHull ℝ face)}
  have hsT : s ⊆ T := by
    intro y hy
    exact ⟨hs y hy,fun h => subset_convexHull ℝ face (hf y hy h)⟩
  have hconv : Convex ℝ T := by
    intro u hu v hv α β hα hβ hsum
    have hu' : side a b u ≤ 0 ∧ (side a b u = 0 → u ∈ convexHull ℝ face) := hu
    have hv' : side a b v ≤ 0 ∧ (side a b v = 0 → v ∈ convexHull ℝ face) := hv
    change side a b (α • u+β • v) ≤ 0 ∧ _
    rw [side_combo a b u v α β hsum]
    have hαu := mul_nonpos_of_nonneg_of_nonpos hα hu'.1
    have hβv := mul_nonpos_of_nonneg_of_nonpos hβ hv'.1
    refine ⟨add_nonpos hαu hβv,?_⟩
    intro hzero
    by_cases ha : α = 0
    · have hb : β = 1 := by linarith
      simpa [ha,hb] using hv'.2 (by simpa [ha,hb] using hzero)
    by_cases hb : β = 0
    · have ha' : α = 1 := by linarith
      simpa [ha',hb] using hu'.2 (by simpa [ha',hb] using hzero)
    have hαzero : α*side a b u = 0 := by linarith
    have hβzero : β*side a b v = 0 := by linarith
    exact (convex_convexHull ℝ face) (hu'.2 ((mul_eq_zero.mp hαzero).resolve_left ha))
      (hv'.2 ((mul_eq_zero.mp hβzero).resolve_left hb)) hα hβ hsum
  exact ((convexHull_min hsT hconv) hx).2 hz

end
end SpectreGeometry
