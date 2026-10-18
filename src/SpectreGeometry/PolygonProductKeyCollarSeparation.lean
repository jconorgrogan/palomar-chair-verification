module

public import SpectreGeometry.PolygonProductKeyCenterSeparation
public import SpectreGeometry.PolygonProductKeyCollar

@[expose] public section


/-! The actual 56 closed recipe collars are pairwise disjoint.

The reference rectangle has squared radius at most 13/1600000000. Its accepted
affine placement preserves distances, and the independently realized center
certificate gives squared center separation at least 1/8. Consequently even
the closed collars, including every outer face, are disjoint. -/
namespace SpectreGeometry
noncomputable section
open Set

/-- The exact squared-radius bound, retaining the optimized recipe constants. -/
theorem product_key_reference_collar_norm_squared (w : EFour)
    (hw : w ∈ productKeyReferenceCollar) :
    ‖w‖ ^ 2 ≤ (13 : ℝ) / 1600000000 := by
  have ht (j : Fin 3) : (w j.castSucc) ^ 2 ≤ (2 * productKeyEta) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (w j.castSucc))
      (by norm_num [productKeyEta] : 0 ≤ 2 * productKeyEta)).mpr (hw.1 j)
    simpa only [sq_abs] using h
  have hn : (w 3) ^ 2 ≤ productKeyRho ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (w 3))
      (by norm_num [productKeyRho] : 0 ≤ productKeyRho)).mpr hw.2
    simpa only [sq_abs] using h
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  change (w 0) ^ 2 ≤ (2 * productKeyEta) ^ 2 at h0
  change (w 1) ^ 2 ≤ (2 * productKeyEta) ^ 2 at h1
  change (w 2) ^ 2 ≤ (2 * productKeyEta) ^ 2 at h2
  norm_num [productKeyEta,productKeyRho] at h0 h1 h2 hn
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_succ]
  norm_num <;> linarith

/-- A convenient rational radius, strictly larger than the exact bound. -/
theorem product_key_reference_collar_norm (w : EFour)
    (hw : w ∈ productKeyReferenceCollar) : ‖w‖ ≤ (1 : ℝ) / 10000 := by
  apply (sq_le_sq₀ (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1 / 10000)).mp
  exact (product_key_reference_collar_norm_squared w hw).trans (by norm_num)

theorem product_key_collar_dist_squared (s : ProductKeySite) (x : EFour)
    (hx : x ∈ productKeyCollar s) :
    dist x (productKeyCenter s) ^ 2 ≤ (13 : ℝ) / 1600000000 := by
  obtain ⟨w,hw,rfl⟩ := hx
  rw [← productKeyAffineIsometry_zero s,(productKeyAffineIsometry s).isometry.dist_eq,
    dist_zero_right]
  exact product_key_reference_collar_norm_squared w hw

theorem product_key_collar_dist (s : ProductKeySite) (x : EFour)
    (hx : x ∈ productKeyCollar s) :
    dist x (productKeyCenter s) ≤ (1 : ℝ) / 10000 := by
  obtain ⟨w,hw,rfl⟩ := hx
  rw [← productKeyAffineIsometry_zero s,(productKeyAffineIsometry s).isometry.dist_eq,
    dist_zero_right]
  exact product_key_reference_collar_norm w hw

theorem product_key_reference_collar_isClosed : IsClosed productKeyReferenceCollar := by
  have hc (j : Fin 4) : Continuous (fun w : EFour => |w j|) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) j).abs
  have heq : productKeyReferenceCollar =
      (⋂ j : Fin 3, {w : EFour | |w j.castSucc| ≤ 2 * productKeyEta}) ∩
        {w : EFour | |w 3| ≤ productKeyRho} := by
    ext w
    simp [productKeyReferenceCollar]
  rw [heq]
  exact (isClosed_iInter fun j : Fin 3 => isClosed_le (hc j.castSucc) continuous_const).inter
    (isClosed_le (hc 3) continuous_const)

theorem product_key_collar_isClosed (s : ProductKeySite) : IsClosed (productKeyCollar s) := by
  exact (productKeyAffineIsometry s).toHomeomorph.isClosedMap _
    product_key_reference_collar_isClosed

/-- The closed collars are disjoint, not just their interiors. -/
theorem product_key_collars_disjoint (s t : ProductKeySite) (hne : s ≠ t) :
    Disjoint (productKeyCollar s) (productKeyCollar t) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hs := product_key_collar_dist s x hx
  have ht := product_key_collar_dist t x hy
  have htri := dist_triangle (productKeyCenter s) x (productKeyCenter t)
  rw [dist_comm (productKeyCenter s) x] at htri
  have hd : dist (productKeyCenter s) (productKeyCenter t) ≤ (1 : ℝ) / 5000 := by
    linarith
  have hd2 := (sq_le_sq₀
    (dist_nonneg : 0 ≤ dist (productKeyCenter s) (productKeyCenter t))
    (by norm_num : (0 : ℝ) ≤ 1 / 5000)).mpr hd
  have hsep := product_key_center_squared_separation s t hne
  norm_num at hd2
  linarith

theorem product_key_collars_pairwise_disjoint :
    Pairwise (fun s t : ProductKeySite => Disjoint (productKeyCollar s) (productKeyCollar t)) :=
  fun s t hne => product_key_collars_disjoint s t hne

end
end SpectreGeometry
