module

public import LiteralPlanar.ArcPoseRegistration
public import LiteralPlanar.CurvedBoundary
public import LiteralPlanar.ThreeVertexRigidity
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section


/-! Proper placement uniqueness for the actual curved body, recovered from
its polynomial arcs and three intrinsic source vertices. No target placement
rigidity or source-body preservation is assumed. -/
namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry

theorem euclideanArc_infinite (e : Fin 14) : (euclideanArc e).Infinite := by
  rw [euclideanArc_eq_chart_image]
  have hi : (Quintic.standardArc Quintic.amplitude).Infinite :=
    (Set.Icc_infinite (by norm_num : (-1/2 : ℝ)<1/2)).image
      (Quintic.standardArc_parameter_injective Quintic.amplitude).injOn
  exact hi.image (edgeChart e).injective.injOn

end
end LiteralPlanar.Candidate

namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry FanBounds Candidate
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)
include p T root

theorem curvedBody_frontier_eq_arcs : frontier curvedBody = ⋃ e : Fin 14, euclideanArc e := by
  rw [curvedBody_frontier p T root]
  simp only [curvedBoundary,Candidate.candidateBoundary,Set.image_iUnion,euclideanArc]

theorem curved_self_isometry_maps_vertices (f : EPlane ≃ᵢ EPlane)
    (hbody : f '' curvedBody = curvedBody) (e : Fin 14) :
    ∃ j : Fin 14, f (euclideanVertex e) = euclideanVertex j := by
  have hfront : f '' frontier curvedBody = frontier curvedBody := by
    simpa only [IsometryEquiv.coe_toHomeomorph,hbody] using f.toHomeomorph.image_frontier curvedBody
  have hsub : f '' euclideanArc e ⊆ ⋃ j : Fin 14, euclideanArc j := by
    intro x hx
    rw [←curvedBody_frontier_eq_arcs p T root,←hfront]
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨y,?_,rfl⟩
    rw [curvedBody_frontier_eq_arcs p T root]
    exact Set.mem_iUnion.mpr ⟨e,hy⟩
  have hinf : (f '' euclideanArc e).Infinite :=
    (euclideanArc_infinite e).image f.injective.injOn
  have hmate : ∃ j : Fin 14, (f '' euclideanArc e ∩ euclideanArc j).Infinite := by
    by_contra hm
    have hf : ∀ j : Fin 14, (f '' euclideanArc e ∩ euclideanArc j).Finite := by
      intro j
      have hh : ¬(f '' euclideanArc e ∩ euclideanArc j).Infinite := fun h => hm ⟨j,h⟩
      exact not_not.mp hh
    apply hinf
    apply (Set.finite_iUnion hf).subset
    intro x hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hsub hx)
    exact Set.mem_iUnion.mpr ⟨j,hx,hj⟩
  obtain ⟨j,hj⟩ := hmate
  have hi : (f '' euclideanArc e ∩ (IsometryEquiv.refl EPlane) '' euclideanArc j).Infinite := by
    change (f '' euclideanArc e ∩ (fun x : EPlane => x) '' euclideanArc j).Infinite
    simpa only [Set.image_id'] using hj
  rcases infinite_placed_edgeArcs_endpoints f (IsometryEquiv.refl EPlane) e j hi with h | h
  · exact ⟨j,h.1⟩
  · exact ⟨next j,h.1⟩

theorem curved_direct_self_isometry_rigid (f : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hbody : f '' curvedBody = curvedBody) :
    ∀ x : EPlane, f x = x := by
  have hm (e : Fin 14) : f (euclideanVertex e) ∈ euclideanBody := by
    obtain ⟨j,hj⟩ := curved_self_isometry_maps_vertices p T root f hbody e
    rw [hj]
    exact ⟨realVertex j,SpectreGeometry.Deformation.source_vertex_mem_body j,rfl⟩
  exact LiteralPlanar.source_direct_rigid_of_three_vertices f hf (hm 6) (hm 12) (hm 0)

end
end LiteralPlanar.Forward
