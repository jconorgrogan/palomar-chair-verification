module

public import LiteralPlanar.CurvedIncidence
public import LiteralPlanar.ArcPoseRegistration

@[expose] public section


/-! Exact inverse decoding on every polynomial arc, including its endpoints.
The two allowed relative poses give the same straight-edge decoding. -/
namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry

theorem edgeChart_flat (e : Fin 14) (t : ℝ) :
    edgeChart e (euclideanCoordinates (t,0)) = euclideanCoordinates
      (interpolate (realVertex e) (realVertex (next e)) (t+1/2)) := by
  rw [edgeChart_apply]
  congr 1
  apply Prod.ext <;>
    simp only [edgeMidpoint,interpolate,realEdge,RealPoint.sub,Prod.fst_add,Prod.snd_add,
      Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

end
end LiteralPlanar.Candidate

namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry Candidate FanBounds Set
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)

def placedInverse (f : EPlane ≃ᵢ EPlane) (x : EPlane) : EPlane :=
  f ((tileHomeomorph p T root).symm (f.symm x))

theorem tileHomeomorph_symm_curve (e : Fin 14) (t : ℝ)
    (ht : -1/2 ≤ t) (ht' : t ≤ 1/2) :
    (tileHomeomorph p T root).symm (euclideanCoordinates (edgeCurve e t)) =
      edgeChart e (euclideanCoordinates (t,0)) := by
  have hb : euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) (t+1/2)) ∈
      euclideanBody := ⟨_,mem_iUnion.mpr ⟨e,polygonEdge_mem_triangleBody e
        ⟨t+1/2,by linarith,by linarith,rfl⟩⟩,rfl⟩
  have h := tileHomeomorph_on_body p T root _ hb
  rw [tileMap_edgeCurve e t ht ht'] at h
  have hi := congrArg (tileHomeomorph p T root).symm h
  simpa only [Homeomorph.symm_apply_apply,edgeChart_flat] using hi.symm

theorem placedInverse_curve (f : EPlane ≃ᵢ EPlane) (e : Fin 14) (t : ℝ)
    (ht : -1/2 ≤ t) (ht' : t ≤ 1/2) :
    placedInverse p T root f (f (euclideanCoordinates (edgeCurve e t))) =
      f (edgeChart e (euclideanCoordinates (t,0))) := by
  simp only [placedInverse,IsometryEquiv.symm_apply_apply,tileHomeomorph_symm_curve p T root e t ht ht']

theorem placedInverse_vertex (f : EPlane ≃ᵢ EPlane) (e : Fin 14) :
    placedInverse p T root f (f (euclideanVertex e)) = f (euclideanVertex e) := by
  have hv := congrArg (tileHomeomorph p T root).symm (tileHomeomorph_at_vertex p T root e)
  simp only [Homeomorph.symm_apply_apply] at hv
  simp only [placedInverse,IsometryEquiv.symm_apply_apply,hv.symm]

theorem placedInverse_image (f : EPlane ≃ᵢ EPlane) :
    placedInverse p T root f '' (f '' curvedBody) = f '' euclideanBody := by
  have hi : (tileHomeomorph p T root).symm '' curvedBody = euclideanBody := by
    rw [←tileHomeomorph_image_body p T root,Set.image_image]
    simp only [Homeomorph.symm_apply_apply,Set.image_id,Set.image_id']
  simp only [placedInverse,Set.image_image,IsometryEquiv.symm_apply_apply]
  rw [←Set.image_image,hi]

theorem placedInverse_agrees_on_matched_arcs (f g : EPlane ≃ᵢ EPlane)
    (e d : Fin 14) (hcontact : (f '' euclideanArc e ∩ g '' euclideanArc d).Infinite)
    (x : EPlane) (hx : x ∈ f '' euclideanArc e) :
    placedInverse p T root f x = placedInverse p T root g x := by
  have himage (q : EPlane ≃ᵢ EPlane) (k : Fin 14) :
      q '' euclideanArc k = (edgeChart k |>.trans q) '' Quintic.standardArc Quintic.amplitude := by
    rw [euclideanArc_eq_chart_image,Set.image_image]
    rfl
  rw [himage,himage] at hcontact
  obtain ⟨y,⟨z,⟨t,ht,rfl⟩,rfl⟩,rfl⟩ := hx
  rcases Quintic.infinite_placed_standardArcs_pose Quintic.amplitude
      (by norm_num [Quintic.amplitude]) _ _ hcontact with hs | hs
  · have hgraph : f (euclideanCoordinates (edgeCurve e t)) =
        g (euclideanCoordinates (edgeCurve d t)) := by
      simpa only [IsometryEquiv.trans_apply,edgeChart_graph] using
        hs (euclideanCoordinates (t,Quintic.height Quintic.amplitude t))
    calc
      _ = f (edgeChart e (euclideanCoordinates (t,0))) := placedInverse_curve p T root f e t ht.1 ht.2
      _ = g (edgeChart d (euclideanCoordinates (t,0))) := hs (euclideanCoordinates (t,0))
      _ = placedInverse p T root g (g (euclideanCoordinates (edgeCurve d t))) :=
        (placedInverse_curve p T root g d t ht.1 ht.2).symm
      _ = _ := congrArg (placedInverse p T root g) hgraph.symm
  · have hneg : -euclideanCoordinates (t,Quintic.height Quintic.amplitude t) =
        euclideanCoordinates (-t,Quintic.height Quintic.amplitude (-t)) := by
      change -coordinateLinearEquiv _ = coordinateLinearEquiv _
      rw [←map_neg,Quintic.height_neg]
      rfl
    have hflat : -euclideanCoordinates (t,0) = euclideanCoordinates (-t,0) := by
      change -coordinateLinearEquiv _ = coordinateLinearEquiv _
      rw [←map_neg]
      simp
    have hgraph : f (euclideanCoordinates (edgeCurve e t)) =
        g (euclideanCoordinates (edgeCurve d (-t))) := by
      simpa only [IsometryEquiv.trans_apply,hneg,edgeChart_graph] using
        hs (euclideanCoordinates (t,Quintic.height Quintic.amplitude t))
    have hn : -1/2 ≤ -t ∧ -t ≤ 1/2 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    calc
      _ = f (edgeChart e (euclideanCoordinates (t,0))) := placedInverse_curve p T root f e t ht.1 ht.2
      _ = g (edgeChart d (euclideanCoordinates (-t,0))) := by
        simpa only [IsometryEquiv.trans_apply,hflat] using hs (euclideanCoordinates (t,0))
      _ = placedInverse p T root g (g (euclideanCoordinates (edgeCurve d (-t)))) :=
        (placedInverse_curve p T root g d (-t) hn.1 hn.2).symm
      _ = _ := congrArg (placedInverse p T root g) hgraph.symm

end
end LiteralPlanar.Forward
