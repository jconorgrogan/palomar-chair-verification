module

public import SpectreGeometry.DeformationHomeomorphismRigidity

@[expose] public section


/-! The accepted source-polygon direct-rigidity calculation in fact needs only
three image-membership tests. This isolates precisely what whole-arc endpoint
recognition must supply for curved placement uniqueness. -/
namespace LiteralPlanar
noncomputable section
open SpectreGeometry SpectreGeometry.Deformation

theorem source_direct_rigid_of_three_vertices (f : EPlane ≃ᵢ EPlane) (hf : DirectPlacement f)
    (h6body : f (euclideanVertex 6) ∈ euclideanBody)
    (h12body : f (euclideanVertex 12) ∈ euclideanBody)
    (h0body : f (euclideanVertex 0) ∈ euclideanBody) : ∀ x : EPlane, f x = x := by
  let F : RealPoint → RealPoint := fun x => euclideanCoordinates.symm (f (euclideanCoordinates x))
  have hF (i : Fin 14) (hi : f (euclideanVertex i) ∈ euclideanBody) :
      F (realVertex i) ∈ polygonBody := by
    obtain ⟨y,hy,he⟩ := hi
    change euclideanCoordinates.symm (f (euclideanVertex i)) ∈ polygonBody
    rw [←he]
    simpa only [Homeomorph.symm_apply_apply] using hy
  have hD : squaredDistance (F (realVertex 6)) (F (realVertex 12)) = diameterSquared := by
    rw [squaredDistance_isometry]
    exact (vertex_diameter_bound 6 12).2.mpr (by decide +kernel)
  have hp := polygon_diameter_unique _ _ (hF 6 h6body)
    (hF 12 h12body) hD
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
    have hlt := polygon_below_three _ (hF 0 h0body)
    rw [h0] at hlt
    have : False := by nlinarith
    exact this.elim

end
end LiteralPlanar
