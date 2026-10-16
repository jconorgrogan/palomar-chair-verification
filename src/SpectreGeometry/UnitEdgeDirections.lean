module

public import SpectreGeometry.PlacedEdgeForms

@[expose] public section


/-! Unit-vector consequences of actual supporting-line alignment. -/
namespace SpectreGeometry
noncomputable section

def quarterTurn (x : RealPoint) : RealPoint := (-x.2,x.1)

theorem dot_det_decomposition (x y : RealPoint) :
    RealPoint.dot x x • y = RealPoint.dot x y • x + RealPoint.det x y • quarterTurn x := by
  apply Prod.ext <;> simp only [RealPoint.dot,RealPoint.det,quarterTurn,Prod.smul_fst,
    Prod.smul_snd,Prod.fst_add,Prod.snd_add,smul_eq_mul] <;> ring

theorem dot_smul_self (x : RealPoint) (c : ℝ) :
    RealPoint.dot (c • x) (c • x) = c^2 * RealPoint.dot x x := by
  simp only [RealPoint.dot,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem unit_collinear_eq_or_neg (x y : RealPoint)
    (hx : RealPoint.dot x x = 1) (hy : RealPoint.dot y y = 1)
    (hdet : RealPoint.det x y = 0) : y = x ∨ y = -x := by
  have he := dot_det_decomposition x y
  rw [hx,hdet,one_smul,zero_smul,add_zero] at he
  have hc : RealPoint.dot x y ^ 2 = 1 := by
    calc
      RealPoint.dot x y ^ 2 = RealPoint.dot x y ^ 2 * RealPoint.dot x x := by rw [hx,mul_one]
      _ = RealPoint.dot (RealPoint.dot x y • x) (RealPoint.dot x y • x) := (dot_smul_self x _).symm
      _ = 1 := by rw [←he,hy]
  rcases sq_eq_one_iff.mp hc with hc | hc
  · exact Or.inl (by simpa [hc] using he)
  · exact Or.inr (by simpa [hc] using he)

theorem coordinate_dot_norm_squared (v : EPlane) :
    RealPoint.dot (euclideanCoordinates.symm v) (euclideanCoordinates.symm v) = ‖v‖^2 := by
  have h0 : euclideanCoordinates (0 : RealPoint) = 0 := coordinateLinearEquiv.map_zero
  have hh := euclideanCoordinates_dist_squared (euclideanCoordinates.symm v) 0
  rw [euclideanCoordinates.apply_symm_apply,h0,dist_zero_right] at hh
  simpa only [RealPoint.sub,Prod.fst_zero,Prod.snd_zero,sub_zero] using hh.symm

theorem displacementPullback_unit (f : EPlane ≃ᵢ EPlane) (v : EPlane) (hv : ‖v‖ = 1) :
    RealPoint.dot (displacementPullback f v) (displacementPullback f v) = 1 := by
  have hh := coordinate_dot_norm_squared (f.symm.toRealLinearIsometryEquiv v)
  rw [LinearIsometryEquiv.norm_map,hv,one_pow] at hh
  exact hh

def placedEdgeVector (f : EPlane ≃ᵢ EPlane) (i : Fin 14) : EPlane :=
  f (euclideanVertex (next i))-f (euclideanVertex i)

theorem placedEdgeVector_unit (f : EPlane ≃ᵢ EPlane) (i : Fin 14) :
    ‖placedEdgeVector f i‖ = 1 := by
  rw [placedEdgeVector,←dist_eq_norm,f.dist_eq]
  exact euclidean_edges_unit i

theorem displacementPullback_edge (f : EPlane ≃ᵢ EPlane) (i : Fin 14) :
    displacementPullback f (placedEdgeVector f i) = realEdge i := by
  rw [placedEdgeVector,displacementPullback_sub,f.symm_apply_apply,f.symm_apply_apply]
  unfold euclideanVertex
  rw [euclideanCoordinates.symm_apply_apply,euclideanCoordinates.symm_apply_apply]
  rfl

theorem unit_edge_kernel_eq_or_neg (f : EPlane ≃ᵢ EPlane) (i : Fin 14) (v : EPlane)
    (hv : ‖v‖ = 1) (hzero : edgeLinearForm f i v = 0) :
    displacementPullback f v = realEdge i ∨ displacementPullback f v = -realEdge i :=
  unit_collinear_eq_or_neg _ _ (real_edges_unit_squared i) (displacementPullback_unit f v hv) hzero

theorem displacementPullback_injective (f : EPlane ≃ᵢ EPlane) :
    Function.Injective (displacementPullback f) :=
  coordinateLinearEquiv.symm.injective.comp f.symm.toRealLinearIsometryEquiv.injective

/-- A unit vector along an actual placed edge line is precisely the edge
vector or its negative. -/
theorem unit_edge_kernel_vector (f : EPlane ≃ᵢ EPlane) (i : Fin 14) (v : EPlane)
    (hv : ‖v‖ = 1) (hzero : edgeLinearForm f i v = 0) :
    v = placedEdgeVector f i ∨ v = -placedEdgeVector f i := by
  rcases unit_edge_kernel_eq_or_neg f i v hv hzero with hp | hn
  · exact Or.inl (displacementPullback_injective f (hp.trans (displacementPullback_edge f i).symm))
  · apply Or.inr
    apply displacementPullback_injective f
    rw [map_neg,displacementPullback_edge]
    exact hn

end
end SpectreGeometry
