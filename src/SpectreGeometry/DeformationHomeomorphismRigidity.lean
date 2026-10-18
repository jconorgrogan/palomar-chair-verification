module

public import SpectreGeometry.DeformationHomeomorphismDiameter
public import SpectreGeometry.DirectIsometryFrames

@[expose] public section


/-! Intrinsic direct-isometry rigidity of the actual source carrier. The
unique diameter pair is preserved, and its possible half-turn is excluded
by a genuine point of the polygon. No slot registration is a hypothesis. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set

theorem coordinateAction_apply (f : EPlane ≃ᵢ EPlane) (x : RealPoint) :
    coordinateAction f x = euclideanCoordinates.symm (f (euclideanCoordinates x)) -
      euclideanCoordinates.symm (f 0) := by
  change coordinateLinearEquiv.symm (f.toRealLinearIsometryEquiv (coordinateLinearEquiv x)) = _
  rw [IsometryEquiv.toRealLinearIsometryEquiv_apply, map_sub]
  rfl

theorem coordinateAction_trans (f g : EPlane ≃ᵢ EPlane) (x : RealPoint) :
    coordinateAction (f.trans g) x = coordinateAction g (coordinateAction f x) := by
  rw [coordinateAction_apply f x, coordinateAction_sub,
    coordinateAction_apply]
  simp only [Homeomorph.apply_symm_apply, IsometryEquiv.trans_apply]

theorem direct_coordinateAction_det (f : EPlane ≃ᵢ EPlane) (hf : DirectPlacement f)
    (x y : RealPoint) :
    RealPoint.det (coordinateAction f x) (coordinateAction f y) = RealPoint.det x y := by
  rw [direct_coordinateAction f hf, direct_coordinateAction f hf]
  have hn := frame_unit_first f
  calc
    _ = RealPoint.dot (frameFirst f) (frameFirst f) * RealPoint.det x y := by
      simp only [complexMulReal, RealPoint.det, RealPoint.dot]
      ring
    _ = _ := by rw [hn, one_mul]

theorem direct_relative (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) : DirectPlacement (f.trans g.symm) := by
  have hh (x : RealPoint) : coordinateAction g (coordinateAction (f.trans g.symm) x) =
      coordinateAction f x := by
    rw [← coordinateAction_trans]
    have he : (f.trans g.symm).trans g = f := by ext x; simp
    rw [he]
  have hd := direct_coordinateAction_det g hg
    (coordinateAction (f.trans g.symm) (1,0))
    (coordinateAction (f.trans g.symm) (0,1))
  rw [hh, hh] at hd
  change 0 < RealPoint.det (coordinateAction (f.trans g.symm) (1,0))
    (coordinateAction (f.trans g.symm) (0,1))
  rw [← hd]
  exact hf

theorem source_vertex_mem_body (i : Fin 14) : realVertex i ∈ polygonBody := by
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  exact subset_convexHull ℝ _ (by simp)

theorem squaredDistance_isometry (f : EPlane ≃ᵢ EPlane) (x y : RealPoint) :
    squaredDistance (euclideanCoordinates.symm (f (euclideanCoordinates x)))
      (euclideanCoordinates.symm (f (euclideanCoordinates y))) = squaredDistance x y := by
  have h := congrArg (fun t : ℝ => t^2) (f.dist_eq (euclideanCoordinates x) (euclideanCoordinates y))
  have hc (a b : RealPoint) : dist (euclideanCoordinates a) (euclideanCoordinates b)^2 =
      squaredDistance a b := by
    rw [euclideanCoordinates_dist_squared]
    simp only [squaredDistance, RealPoint.dot, RealPoint.sub, pow_two]
  rw [← hc, ← hc, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  exact h

theorem source_diameter_coordinates :
    realVertex 6 = ((6+Real.sqrt 3)/2, 3/2) ∧
    realVertex 12 = (-Real.sqrt 3/2, 3/2) ∧
    realVertex 0 = (0,0) := by
  norm_num [realVertex,realize,vertex,vertices,Quad3.eval]

theorem source_direct_isometry_rigid (f : EPlane ≃ᵢ EPlane) (hf : DirectPlacement f)
    (hbody : f '' euclideanBody ⊆ euclideanBody) : ∀ x : EPlane, f x = x := by
  let F : RealPoint → RealPoint := fun x => euclideanCoordinates.symm (f (euclideanCoordinates x))
  have hF (x : RealPoint) (hx : x ∈ polygonBody) : F x ∈ polygonBody := by
    obtain ⟨y,hy,he⟩ := hbody ⟨euclideanCoordinates x,⟨x,hx,rfl⟩,rfl⟩
    simpa only [F,←he,Homeomorph.symm_apply_apply] using hy
  have hD : squaredDistance (F (realVertex 6)) (F (realVertex 12)) = diameterSquared := by
    rw [squaredDistance_isometry]
    exact (vertex_diameter_bound 6 12).2.mpr (by decide +kernel)
  have hp := polygon_diameter_unique _ _ (hF _ (source_vertex_mem_body 6))
    (hF _ (source_vertex_mem_body 12)) hD
  have hs : 0 < 3+Real.sqrt 3 := by positivity
  obtain ⟨h6,h12,h0⟩ := source_diameter_coordinates
  have hlin (x y : RealPoint) : complexMulReal (frameFirst f) (y-x) = F y-F x := by
    rw [←direct_coordinateAction f hf, coordinateAction_sub]
  rcases hp with hp | hp
  · have he := hlin (realVertex 12) (realVertex 6)
    rw [hp.1,hp.2,h6,h12] at he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    simp only [complexMulReal,Prod.fst_sub,Prod.snd_sub] at he1 he2
    have ha : (frameFirst f).1=1 := by nlinarith
    have hb : (frameFirst f).2=0 := by nlinarith
    intro x
    obtain ⟨p,rfl⟩ := euclideanCoordinates.surjective x
    apply euclideanCoordinates.symm.injective
    change F p = p
    have hp' := hlin (realVertex 6) p
    rw [hp.1] at hp'
    simp only [complexMulReal,ha,hb,one_mul,zero_mul,sub_zero,add_zero] at hp'
    change p-realVertex 6 = F p-realVertex 6 at hp'
    exact (sub_left_inj.mp hp').symm
  · have he := hlin (realVertex 12) (realVertex 6)
    rw [hp.1,hp.2,h6,h12] at he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    simp only [complexMulReal,Prod.fst_sub,Prod.snd_sub] at he1 he2
    have ha : (frameFirst f).1= -1 := by nlinarith
    have hb : (frameFirst f).2=0 := by nlinarith
    have hp' := hlin (realVertex 6) (realVertex 0)
    rw [hp.1,h6,h12,h0] at hp'
    have hy := congrArg Prod.snd hp'
    simp only [complexMulReal,Prod.fst_sub,Prod.snd_sub,ha,hb] at hy
    have hlt := polygon_below_three _ (hF _ (source_vertex_mem_body 0))
    rw [h0] at hlt
    have : False := by nlinarith
    exact this.elim

/-- Equality of literal source carriers recovers the full direct placement. -/
theorem direct_placement_eq_of_carrier_eq (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g)
    (hbody : f '' euclideanBody = g '' euclideanBody) : f = g := by
  have hs : (f.trans g.symm) '' euclideanBody ⊆ euclideanBody := by
    rintro _ ⟨x,hx,rfl⟩
    have hfx : f x ∈ g '' euclideanBody := hbody ▸ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hfx
    simpa only [IsometryEquiv.trans_apply,←he,IsometryEquiv.symm_apply_apply] using hy
  have hh := source_direct_isometry_rigid (f.trans g.symm) (direct_relative f g hf hg) hs
  apply IsometryEquiv.ext
  intro x
  have he := congrArg g (hh x)
  simpa using he

end
end SpectreGeometry.Deformation
