module

public import SpectreGeometry.PolygonProductKeySeparationData
public import SpectreGeometry.PolygonProductKeyFrames

@[expose] public section


/-! Sound real realization of the finite exact product-key separation data.
The conclusion concerns the actual 56 recipe centers in Euclidean four-space.
It does not require or assert anything about a keyed body. -/
namespace SpectreGeometry
noncomputable section

def productKeyPlanarSquaredDistance (x y : RealPoint) : ℝ :=
  RealPoint.dot (RealPoint.sub x y) (RealPoint.sub x y)

private theorem planar_squared_distance_self (x : RealPoint) :
    productKeyPlanarSquaredDistance x x = 0 := by
  simp [productKeyPlanarSquaredDistance,RealPoint.sub,RealPoint.dot]

private theorem planar_squared_distance_comm (x y : RealPoint) :
    productKeyPlanarSquaredDistance x y = productKeyPlanarSquaredDistance y x := by
  simp only [productKeyPlanarSquaredDistance,RealPoint.sub,RealPoint.dot]
  ring

private theorem quad_nonnegative_sound {q : Quad3} (h : productKeyQuadNonnegative q) :
    0 ≤ Quad3.eval q := by
  rcases h with h | h
  · rw [h]
    norm_num [Quad3.eval]
  · exact (Quad3.positive_sound _ h).le

/-- The exact numerator really is eight times the accepted active center. -/
theorem product_key_center_numerator_eval (b : Fin 2) (i : Fin 14) (e : Bool) :
    ExactPoint.eval (productKeyCenterNumerator i e) =
      (8 : ℝ) • productKeyActiveCenter (b,i,e) := by
  cases e <;> ext <;>
    simp [productKeyCenterNumerator,productKeyExactScale,ExactPoint.add,ExactPoint.eval,
      productKeyActiveCenter,productKeySign,edge,ExactPoint.sub,realEdge,realVertex,realize,
      RealPoint.sub,Quad3.eval,Quad3.add,Quad3.sub,Quad3.mul] <;> ring

private theorem numerator_distance_eval (b c : Fin 2) (i j : Fin 14) (e f : Bool) :
    Quad3.eval (productKeyNumeratorDistanceSquared i j e f) =
      64 * productKeyPlanarSquaredDistance
        (productKeyActiveCenter (b,i,e)) (productKeyActiveCenter (c,j,f)) := by
  unfold productKeyNumeratorDistanceSquared
  rw [ExactPoint.eval_dot,ExactPoint.eval_sub,
    product_key_center_numerator_eval b i e,product_key_center_numerator_eval c j f]
  simp only [productKeyPlanarSquaredDistance,RealPoint.dot,RealPoint.sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

private theorem passive_numerator_distance_eval (b : Fin 2) (i : Fin 14) (e : Bool) :
    Quad3.eval (productKeyPassiveNumeratorDistanceSquared i e) =
      64 * productKeyPlanarSquaredDistance (productKeyActiveCenter (b,i,e)) (1/2,1/2) := by
  unfold productKeyPassiveNumeratorDistanceSquared
  rw [ExactPoint.eval_dot,ExactPoint.eval_sub,product_key_center_numerator_eval b i e]
  norm_num [productKeyPlanarSquaredDistance,RealPoint.dot,RealPoint.sub,
    ExactPoint.eval,Quad3.eval] <;> ring

/-- Distinct edge/polarity sites on the active polygon have squared distance
at least 1/8, with no real-number finite case split. -/
theorem product_key_active_center_squared_separation
    (b c : Fin 2) (i j : Fin 14) (e f : Bool) (hne : (i,e) ≠ (j,f)) :
    (1 : ℝ) / 8 ≤ productKeyPlanarSquaredDistance
      (productKeyActiveCenter (b,i,e)) (productKeyActiveCenter (c,j,f)) := by
  have h := quad_nonnegative_sound (product_key_numerator_separation i j e f hne)
  rw [Quad3.eval_sub,numerator_distance_eval b c i j e f] at h
  norm_num [Quad3.eval] at h
  linarith

theorem product_key_active_passive_squared_separation (b : Fin 2) (i : Fin 14) (e : Bool) :
    (5 : ℝ) / 16 ≤ productKeyPlanarSquaredDistance
      (productKeyActiveCenter (b,i,e)) (1/2,1/2) := by
  have h := quad_nonnegative_sound (product_key_passive_numerator_separation i e)
  rw [Quad3.eval_sub,passive_numerator_distance_eval b i e] at h
  norm_num [Quad3.eval] at h
  linarith

theorem product_key_product_coordinates_dist_squared (a b c d : RealPoint) :
    dist (productCoordinates (a,b)) (productCoordinates (c,d)) ^ 2 =
      productKeyPlanarSquaredDistance a c + productKeyPlanarSquaredDistance b d := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_succ,Real.dist_eq,productCoordinates,productCoordinateLinearEquiv,
    productKeyPlanarSquaredDistance,RealPoint.dot,RealPoint.sub,pow_two] <;> ring

/-- Every pair of distinct actual recipe centers is separated by squared
Euclidean distance at least 1/8. This includes opposite polarities and factors. -/
theorem product_key_center_squared_separation (s t : ProductKeySite) (hne : s ≠ t) :
    (1 : ℝ) / 8 ≤ dist (productKeyCenter s) (productKeyCenter t) ^ 2 := by
  rcases s with ⟨b,i,e⟩
  rcases t with ⟨c,j,f⟩
  fin_cases b <;> fin_cases c
  · have hne' : (i,e) ≠ (j,f) := by
      intro h
      apply hne
      exact congrArg (fun p : Fin 14 × Bool => ((0 : Fin 2),p)) h
    change (1 : ℝ) / 8 ≤ dist (productKeyCenter (0,i,e)) (productKeyCenter (0,j,f)) ^ 2
    rw [productKeyCenter_left,productKeyCenter_left,product_key_product_coordinates_dist_squared]
    change 1 / 8 ≤ productKeyPlanarSquaredDistance (productKeyActiveCenter (0,i,e))
      (productKeyActiveCenter (0,j,f)) + productKeyPlanarSquaredDistance (1/2,1/2) (1/2,1/2)
    rw [planar_squared_distance_self,add_zero]
    exact product_key_active_center_squared_separation 0 0 i j e f hne'
  · change (1 : ℝ) / 8 ≤ dist (productKeyCenter (0,i,e)) (productKeyCenter (1,j,f)) ^ 2
    rw [productKeyCenter_left,productKeyCenter_right,product_key_product_coordinates_dist_squared]
    change 1 / 8 ≤ productKeyPlanarSquaredDistance (productKeyActiveCenter (0,i,e)) (1/2,1/2) +
      productKeyPlanarSquaredDistance (1/2,1/2) (productKeyActiveCenter (1,j,f))
    rw [planar_squared_distance_comm (1/2,1/2)]
    linarith [product_key_active_passive_squared_separation 0 i e,
      product_key_active_passive_squared_separation 1 j f]
  · change (1 : ℝ) / 8 ≤ dist (productKeyCenter (1,i,e)) (productKeyCenter (0,j,f)) ^ 2
    rw [productKeyCenter_right,productKeyCenter_left,product_key_product_coordinates_dist_squared]
    change 1 / 8 ≤ productKeyPlanarSquaredDistance (1/2,1/2) (productKeyActiveCenter (0,j,f)) +
      productKeyPlanarSquaredDistance (productKeyActiveCenter (1,i,e)) (1/2,1/2)
    rw [planar_squared_distance_comm (1/2,1/2)]
    linarith [product_key_active_passive_squared_separation 0 j f,
      product_key_active_passive_squared_separation 1 i e]
  · have hne' : (i,e) ≠ (j,f) := by
      intro h
      apply hne
      exact congrArg (fun p : Fin 14 × Bool => ((1 : Fin 2),p)) h
    change (1 : ℝ) / 8 ≤ dist (productKeyCenter (1,i,e)) (productKeyCenter (1,j,f)) ^ 2
    rw [productKeyCenter_right,productKeyCenter_right,product_key_product_coordinates_dist_squared]
    change 1 / 8 ≤ productKeyPlanarSquaredDistance (1/2,1/2) (1/2,1/2) +
      productKeyPlanarSquaredDistance (productKeyActiveCenter (1,i,e)) (productKeyActiveCenter (1,j,f))
    rw [planar_squared_distance_self,zero_add]
    exact product_key_active_center_squared_separation 1 1 i j e f hne'

/-- In particular, the source's 56 indexed centers are genuinely distinct. -/
theorem product_key_center_injective : Function.Injective productKeyCenter := by
  intro s t h
  by_contra hne
  have hd := product_key_center_squared_separation s t hne
  rw [h,dist_self] at hd
  norm_num at hd

end
end SpectreGeometry
