module

public import SpectreGeometry.PolygonProductKeyFrames
public import SpectreGeometry.FanSeparation

@[expose] public section


/-! Explicit quantitative margins for the actual optimized product-key collars.
These margins use the native polygon fan, whose center is unrelated to the
passive product anchor (1/2,1/2). -/
namespace SpectreGeometry
noncomputable section

def productKeyPlanarOutward (i : Fin 14) : RealPoint :=
  ((realEdge i).2,-(realEdge i).1)

def productKeyFanHeight (i : Fin 14) : ℝ :=
  side (realVertex i) (realVertex (next i)) realFanCenter

private theorem sqrt_three_bounds : (5 : ℝ) / 3 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 7 / 4 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

/-- Edge 7 has the smallest height, so the weaker 1/16 margin is deliberate. -/
theorem product_key_fan_height_margin (i : Fin 14) : 1 / 16 ≤ productKeyFanHeight i := by
  have hs := sqrt_three_bounds
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases i <;>
    norm_num [productKeyFanHeight,side,realVertex,realFanCenter,realize,vertex,vertices,
      next,fanCenter,Quad3.eval,RealPoint.sub,RealPoint.det] <;> nlinarith [hs.1,hs.2]

theorem product_key_radial_coordinate_bound (i : Fin 14) :
    |(RealPoint.sub (realVertex i) realFanCenter).1| ≤ 5 ∧
      |(RealPoint.sub (realVertex i) realFanCenter).2| ≤ 5 := by
  have hs := sqrt_three_bounds
  constructor <;> apply abs_le.mpr <;> constructor <;> fin_cases i <;>
    norm_num [realVertex,realFanCenter,realize,vertex,vertices,fanCenter,
      Quad3.eval,RealPoint.sub] <;> nlinarith [hs.1,hs.2]

theorem product_key_edge_coordinate_bound (i : Fin 14) :
    |(realEdge i).1| ≤ 1 ∧ |(realEdge i).2| ≤ 1 := by
  have hu := real_edges_unit_squared i
  simp only [RealPoint.dot] at hu
  constructor <;> apply abs_le.mpr <;> constructor <;> nlinarith [sq_nonneg (realEdge i).1,sq_nonneg (realEdge i).2]

private theorem det_bound_ten (a b : RealPoint)
    (ha : |a.1| ≤ 5 ∧ |a.2| ≤ 5) (hb : |b.1| ≤ 1 ∧ |b.2| ≤ 1) :
    |RealPoint.det a b| ≤ 10 := by
  have h1 : |a.1 * b.2| ≤ 5 := by
    rw [abs_mul]
    exact (mul_le_mul ha.1 hb.2 (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have h2 : |a.2 * b.1| ≤ 5 := by
    rw [abs_mul]
    exact (mul_le_mul ha.2 hb.1 (abs_nonneg _) (by norm_num)).trans (by norm_num)
  exact (abs_sub _ _).trans (by linarith)

theorem product_key_radial_edge_coefficient_bound (i j : Fin 14) :
    |RealPoint.det (RealPoint.sub (realVertex j) realFanCenter) (realEdge i)| ≤ 10 :=
  det_bound_ten _ _ (product_key_radial_coordinate_bound j) (product_key_edge_coordinate_bound i)

theorem product_key_radial_normal_coefficient_bound (i j : Fin 14) :
    |RealPoint.det (RealPoint.sub (realVertex j) realFanCenter) (productKeyPlanarOutward i)| ≤ 10 := by
  apply det_bound_ten _ _ (product_key_radial_coordinate_bound j)
  have h := product_key_edge_coordinate_bound i
  simpa [productKeyPlanarOutward,abs_neg] using And.intro h.2 h.1

theorem product_key_sign_abs (s : ProductKeySite) : |productKeySign s| = 1 := by
  unfold productKeySign
  split <;> norm_num

theorem product_key_active_parameter_bounds (s : ProductKeySite) :
    1 / 4 ≤ 1 / 2 - productKeySign s / 4 ∧
      1 / 2 - productKeySign s / 4 ≤ 3 / 4 := by
  unfold productKeySign
  split <;> norm_num

theorem product_key_active_radial_left (s : ProductKeySite) :
    radialSide s.2.1 (productKeyActiveCenter s) =
      (1 / 2 - productKeySign s / 4) * productKeyFanHeight s.2.1 := by
  simp only [radialSide,productKeyActiveCenter,productKeyFanHeight,realEdge,side,
    RealPoint.det,RealPoint.sub,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem product_key_active_radial_right (s : ProductKeySite) :
    radialSide (next s.2.1) (productKeyActiveCenter s) =
      -(1 / 2 + productKeySign s / 4) * productKeyFanHeight s.2.1 := by
  simp only [radialSide,productKeyActiveCenter,productKeyFanHeight,realEdge,side,
    RealPoint.det,RealPoint.sub,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem product_key_active_radial_margins (s : ProductKeySite) :
    1 / 64 ≤ radialSide s.2.1 (productKeyActiveCenter s) ∧
      radialSide (next s.2.1) (productKeyActiveCenter s) ≤ -(1 / 64) := by
  rw [product_key_active_radial_left,product_key_active_radial_right]
  have ht := product_key_active_parameter_bounds s
  have hf := product_key_fan_height_margin s.2.1
  have hp : 0 ≤ productKeyFanHeight s.2.1 := by linarith
  have h1 := mul_nonneg (sub_nonneg.mpr ht.1) hp
  have h2 := mul_nonneg (sub_nonneg.mpr ht.2) hp
  constructor <;> nlinarith

end
end SpectreGeometry
