module

public import SpectreGeometry.PolygonProductKeyFactorBoundary
public import SpectreGeometry.DirectIsometryFrames

@[expose] public section


/-! Full two-block transition fixed by an actual registered key. The planar
transition is an explicit proper Euclidean isometry; the passive factor is
pointwise unchanged. No global contact connectivity or factor coverage enters. -/
namespace SpectreGeometry
noncomputable section
open Set

set_option backward.privateInPublic true in
private def complexConjugate (a : RealPoint) : RealPoint := (a.1,-a.2)

private theorem unit_complex_inverse (a x : RealPoint) (ha : RealPoint.dot a a = 1) :
    complexMulReal (complexConjugate a) (complexMulReal a x) = x ∧
      complexMulReal a (complexMulReal (complexConjugate a) x) = x := by
  have hx := congrArg (fun t : ℝ => t*x.1) ha
  have hy := congrArg (fun t : ℝ => t*x.2) ha
  constructor <;> apply Prod.ext <;> simp only [complexMulReal,complexConjugate,RealPoint.dot] at * <;> nlinarith

set_option backward.privateInPublic true in
private def unitComplexEquiv (a v : RealPoint) (ha : RealPoint.dot a a = 1) : RealPoint ≃ RealPoint where
  toFun x := v+complexMulReal a x
  invFun x := complexMulReal (complexConjugate a) (x-v)
  left_inv x := by simpa only [add_sub_cancel_left] using (unit_complex_inverse a x ha).1
  right_inv x := by
    change v+complexMulReal a (complexMulReal (complexConjugate a) (x-v)) = x
    rw [(unit_complex_inverse a (x-v) ha).2]
    abel

set_option backward.privateInPublic true in
private def unitComplexEuclideanEquiv (a v : RealPoint) (ha : RealPoint.dot a a = 1) : EPlane ≃ EPlane :=
  euclideanCoordinates.symm.toEquiv.trans ((unitComplexEquiv a v ha).trans euclideanCoordinates.toEquiv)

private theorem unitComplex_dist (a v : RealPoint) (ha : RealPoint.dot a a = 1) (x y : EPlane) :
    dist (unitComplexEuclideanEquiv a v ha x) (unitComplexEuclideanEquiv a v ha y) = dist x y := by
  obtain ⟨p,rfl⟩ := euclideanCoordinates.surjective x
  obtain ⟨q,rfl⟩ := euclideanCoordinates.surjective y
  have hs : dist (unitComplexEuclideanEquiv a v ha (euclideanCoordinates p))
      (unitComplexEuclideanEquiv a v ha (euclideanCoordinates q))^2 =
      dist (euclideanCoordinates p) (euclideanCoordinates q)^2 := by
    change dist (euclideanCoordinates (v+complexMulReal a p))
      (euclideanCoordinates (v+complexMulReal a q))^2 = _
    rw [euclideanCoordinates_dist_squared,euclideanCoordinates_dist_squared]
    have he : RealPoint.sub (v+complexMulReal a p) (v+complexMulReal a q) =
        complexMulReal a (RealPoint.sub p q) := by
      apply Prod.ext <;> simp [RealPoint.sub,complexMulReal] <;> ring
    rw [he,complexMulReal_dot_self,ha,one_mul]
  nlinarith [dist_nonneg (x:=unitComplexEuclideanEquiv a v ha (euclideanCoordinates p))
    (y:=unitComplexEuclideanEquiv a v ha (euclideanCoordinates q)),
    dist_nonneg (x:=euclideanCoordinates p) (y:=euclideanCoordinates q)]

set_option backward.privateInPublic true in
private def unitComplexPlacement (a v : RealPoint) (ha : RealPoint.dot a a = 1) : EPlane ≃ᵢ EPlane where
  toEquiv := unitComplexEuclideanEquiv a v ha
  isometry_toFun := Isometry.of_dist_eq (unitComplex_dist a v ha)

private theorem unitComplexPlacement_apply (a v x : RealPoint) (ha : RealPoint.dot a a = 1) :
    unitComplexPlacement a v ha (euclideanCoordinates x) = euclideanCoordinates (v+complexMulReal a x) := rfl

private theorem unitComplexPlacement_direct (a v : RealPoint) (ha : RealPoint.dot a a = 1) :
    DirectPlacement (unitComplexPlacement a v ha) := by
  have hc (x : RealPoint) : coordinateAction (unitComplexPlacement a v ha) x = complexMulReal a x := by
    change coordinateLinearEquiv.symm ((unitComplexPlacement a v ha).toRealLinearIsometryEquiv
      (coordinateLinearEquiv x)) = _
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply,map_sub]
    change (v+complexMulReal a x)-(v+complexMulReal a (0:RealPoint)) = _
    simp [complexMulReal]
  change 0 < RealPoint.det (coordinateAction (unitComplexPlacement a v ha) (1,0))
    (coordinateAction (unitComplexPlacement a v ha) (0,1))
  rw [hc,hc]
  simp only [RealPoint.det,complexMulReal,RealPoint.dot] at ha ⊢
  nlinarith

set_option backward.privateInPublic true in
def productActiveEdgeRotation (i j : Fin 14) : RealPoint :=
  -complexMulReal (realEdge j) (complexConjugate (realEdge i))

theorem product_active_edge_rotation_unit (i j : Fin 14) :
    RealPoint.dot (productActiveEdgeRotation i j) (productActiveEdgeRotation i j) = 1 := by
  have hi := real_edges_unit_squared i
  have hj := real_edges_unit_squared j
  have hc : RealPoint.dot (complexConjugate (realEdge i)) (complexConjugate (realEdge i)) = 1 := by
    simpa [complexConjugate,RealPoint.dot] using hi
  change RealPoint.dot (-complexMulReal (realEdge j) (complexConjugate (realEdge i)))
    (-complexMulReal (realEdge j) (complexConjugate (realEdge i))) = 1
  have hn (z : RealPoint) : RealPoint.dot (-z) (-z) = RealPoint.dot z z := by simp [RealPoint.dot]
  rw [hn,complexMulReal_dot_self,hj,hc,mul_one]

set_option backward.privateInPublic true in
def productActiveEdgeTransition (i j : Fin 14) : EPlane ≃ᵢ EPlane :=
  unitComplexPlacement (productActiveEdgeRotation i j)
    (realVertex j+realEdge j-complexMulReal (productActiveEdgeRotation i j) (realVertex i))
    (product_active_edge_rotation_unit i j)

theorem product_active_edge_transition_apply (i j : Fin 14) (x : RealPoint) :
    productActiveEdgeTransition i j (euclideanCoordinates x) =
      euclideanCoordinates (realVertex j+realEdge j+
        complexMulReal (productActiveEdgeRotation i j) (x-realVertex i)) := by
  rw [productActiveEdgeTransition,unitComplexPlacement_apply]
  congr 1
  apply Prod.ext <;> simp [complexMulReal] <;> ring

theorem product_active_edge_transition_direct (i j : Fin 14) :
    DirectPlacement (productActiveEdgeTransition i j) :=
  unitComplexPlacement_direct _ _ _

def productFactorPoint (b : Fin 2) (a p : RealPoint) : EFour :=
  if b = 0 then productCoordinates (a,p) else productCoordinates (p,a)

def productEdgeFramePoint (i : Fin 14) (r h : ℝ) : RealPoint :=
  realVertex i+r • realEdge i+h • ((realEdge i).2,-(realEdge i).1)

def productKeyFullReference (s : ProductKeySite) (r h : ℝ) (p : RealPoint) : EFour :=
  WithLp.toLp 2 ![productKeySign s*(r-1/2)+1/4,p.1-1/2,p.2-1/2,productKeySign s*h]

theorem product_key_signed_full_reference (s : ProductKeySite) (r h : ℝ) (p : RealPoint) :
    productKeySignedAffineIsometry s (productKeyFullReference s r h p) =
      productFactorPoint s.1 (productEdgeFramePoint s.2.1 r h) p := by
  rw [product_key_signed_pose_apply,productKeyAffineIsometry_apply]
  rcases s with ⟨b,i,e⟩
  fin_cases b <;> cases e <;> ext k <;> fin_cases k <;>
    simp [productKeyFullReference,productFactorPoint,productEdgeFramePoint,
      product_key_normal_reflection_coordinate,productKeyCenter,productKeyActiveCenter,
      productKeyFrame,productKeyTangent,productKeyOutwardNormal,productKeySign,
      leftNormalMap,rightNormalMap,productCoordinates,productCoordinateLinearEquiv,
      Fin.sum_univ_succ] <;> ring

theorem registered_product_full_coordinates (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour) (hsign : productKeySign t = -productKeySign s)
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g)
    (r h : ℝ) (p : RealPoint) :
    f (productFactorPoint s.1 (productEdgeFramePoint s.2.1 r h) p) =
      g (productFactorPoint t.1 (productEdgeFramePoint t.2.1 (1-r) (-h)) p) := by
  have hw : productKeyFullReference s r h p = productKeyFullReference t (1-r) (-h) p := by
    ext k; fin_cases k <;> simp [productKeyFullReference,hsign] <;> ring
  have he := congrArg (fun k : EFour ≃ᵢ EFour => k (productKeyFullReference s r h p)) hp
  change f (productKeySignedAffineIsometry s (productKeyFullReference s r h p)) =
    g (productKeySignedAffineIsometry t (productKeyFullReference s r h p)) at he
  rw [hw,product_key_signed_full_reference] at he
  rw [← product_key_signed_full_reference s,hw]
  exact he

theorem product_edge_frame_surjective (i : Fin 14) (a : RealPoint) :
    ∃ r h : ℝ, productEdgeFramePoint i r h = a := by
  let d := a-realVertex i
  refine ⟨RealPoint.dot (realEdge i) d,
    RealPoint.dot ((realEdge i).2,-(realEdge i).1) d,?_⟩
  have hu := real_edges_unit_squared i
  have h1 := congrArg (fun t : ℝ => t*d.1) hu
  have h2 := congrArg (fun t : ℝ => t*d.2) hu
  apply Prod.ext <;> simp only [productEdgeFramePoint,RealPoint.dot,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at * <;> dsimp [d] at * <;> nlinarith

theorem product_active_edge_transition_frame (i j : Fin 14) (r h : ℝ) :
    productActiveEdgeTransition i j (euclideanCoordinates (productEdgeFramePoint i r h)) =
      euclideanCoordinates (productEdgeFramePoint j (1-r) (-h)) := by
  rw [product_active_edge_transition_apply]
  have hu := real_edges_unit_squared i
  have h1 := congrArg (fun t : ℝ => t*r*(realEdge j).1) hu
  have h2 := congrArg (fun t : ℝ => t*r*(realEdge j).2) hu
  have h3 := congrArg (fun t : ℝ => t*h*(realEdge j).1) hu
  have h4 := congrArg (fun t : ℝ => t*h*(realEdge j).2) hu
  congr 1
  apply Prod.ext <;> simp only [productEdgeFramePoint,productActiveEdgeRotation,complexMulReal,
    complexConjugate,RealPoint.dot,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
    Prod.fst_neg,Prod.snd_neg,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at * <;> nlinarith

/-- A registered key fixes the complete passive coordinate and a proper
active planar isometry on the entire ambient space. -/
theorem registered_product_factor_transition (s t : ProductKeySite)
    (f g : EFour ≃ᵢ EFour) (hsign : productKeySign t = -productKeySign s)
    (hp : (productKeySignedAffineIsometry s).toIsometryEquiv.trans f =
      (productKeySignedAffineIsometry t).toIsometryEquiv.trans g)
    (a p : RealPoint) :
    f (productFactorPoint s.1 a p) = g (productFactorPoint t.1
      (euclideanCoordinates.symm (productActiveEdgeTransition s.2.1 t.2.1 (euclideanCoordinates a))) p) := by
  obtain ⟨r,h,rfl⟩ := product_edge_frame_surjective s.2.1 a
  rw [product_active_edge_transition_frame,Homeomorph.symm_apply_apply]
  exact registered_product_full_coordinates s t f g hsign hp r h p

end
end SpectreGeometry
