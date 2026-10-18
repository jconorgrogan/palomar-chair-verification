module

public import SpectreGeometry.ReverseAnchorHomeomorphism

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open scoped NNReal

/-- A uniform ordinary product-metric bound for the actual interpolation.
It is useful for bounding its distance from a cluster-wise realization. -/
theorem anchorInterpolation_lipschitz (A : ℤ × ℤ → AnchorPlane) (hA : AnchorResidualBounds A) :
    LipschitzWith 32 (anchorInterpolation A) := by
  have h11 : ∀ n m, |(A (n+1,m)).1-(A (n,m)).1| ≤ (24:ℝ) := by
    intro n m
    have h := abs_le.mp (hA.horizontal_first n m)
    apply abs_le.mpr
    constructor <;> linarith
  have h12 : ∀ n m, |(A (n,m+1)).1-(A (n,m)).1| ≤ (6:ℝ) := by
    intro n m
    have h := abs_le.mp (hA.vertical_first n m)
    apply abs_le.mpr
    constructor <;> linarith
  have h21 : ∀ n m, |(A (n+1,m)).2-(A (n,m)).2| ≤ (6:ℝ) := by
    intro n m
    have h := abs_le.mp (hA.horizontal_second n m)
    apply abs_le.mpr
    constructor <;> linarith
  have h22 : ∀ n m, |(A (n,m+1)).2-(A (n,m)).2| ≤ (26:ℝ) := by
    intro n m
    have h := abs_le.mp (hA.vertical_second n m)
    apply abs_le.mpr
    constructor <;> linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : dist x.1 y.1 ≤ dist x y := le_max_left _ _
  have hy : dist x.2 y.2 ≤ dist x y := le_max_right _ _
  change max (dist (gridInterpolate (fun p => (A p).1) x) (gridInterpolate (fun p => (A p).1) y))
    (dist (gridInterpolate (fun p => (A p).2) x) (gridInterpolate (fun p => (A p).2) y)) ≤ _
  apply max_le
  · have h := gridInterpolate_two_coordinate_bound (fun p => (A p).1) 24 6 h11 h12 x y
    norm_num at h ⊢
    linarith [show (0:ℝ) ≤ dist x y from dist_nonneg]
  · have h := gridInterpolate_two_coordinate_bound (fun p => (A p).2) 6 26 h21 h22 x y
    norm_num at h ⊢
    linarith

/-- Pointwise carrier control plus a bounded source-cell radius is enough
for the bounded-distance hypothesis in the properness argument. -/
theorem distance_from_anchorInterpolation (A : ℤ × ℤ → AnchorPlane)
    (hA : AnchorResidualBounds A) (F : AnchorPlane → AnchorPlane) (R r : ℝ)
    (h : ∀ x, ∃ n m : ℤ, dist x ((n:ℝ),(m:ℝ)) ≤ r ∧ dist (F x) (A (n,m)) ≤ R)
    (x : AnchorPlane) : dist (F x) (anchorInterpolation A x) ≤ R+32*r := by
  obtain ⟨n,m,hx,hF⟩ := h x
  have hL := (anchorInterpolation_lipschitz A hA).dist_le_mul ((n:ℝ),(m:ℝ)) x
  have he : anchorInterpolation A ((n:ℝ),(m:ℝ)) = A (n,m) := by
    simp [anchorInterpolation]
  rw [he,dist_comm ((n:ℝ),(m:ℝ)) x] at hL
  norm_num at hL
  calc
    _ ≤ dist (F x) (A (n,m))+dist (A (n,m)) (anchorInterpolation A x) := dist_triangle _ _ _
    _ ≤ R+32*r := by linarith

end
end SpectreGeometry.ReverseExistence
