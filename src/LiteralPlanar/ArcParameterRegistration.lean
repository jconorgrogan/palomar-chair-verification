module

public import LiteralPlanar.ArcPoseRegistration

@[expose] public section


/-! Whole polynomial arc recognition fixes the full parameterization, not
merely the unordered endpoints. Both surviving proper poses are retained. -/
namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry

theorem infinite_placed_edgeArcs_parameters (f g : EPlane ≃ᵢ EPlane)
    (e j : Fin 14) (h : (f '' euclideanArc e ∩ g '' euclideanArc j).Infinite) :
    (∀ t : ℝ, f (euclideanCoordinates (edgeCurve e t)) =
      g (euclideanCoordinates (edgeCurve j t))) ∨
    (∀ t : ℝ, f (euclideanCoordinates (edgeCurve e t)) =
      g (euclideanCoordinates (edgeCurve j (-t)))) := by
  have himage (q : EPlane ≃ᵢ EPlane) (k : Fin 14) :
      q '' euclideanArc k = (edgeChart k |>.trans q) '' Quintic.standardArc Quintic.amplitude := by
    rw [euclideanArc_eq_chart_image,Set.image_image]
    rfl
  rw [himage,himage] at h
  rcases Quintic.infinite_placed_standardArcs_pose Quintic.amplitude
      (by norm_num [Quintic.amplitude]) _ _ h with hs | hs
  · left
    intro t
    simpa only [IsometryEquiv.trans_apply,edgeChart_graph] using
      hs (euclideanCoordinates (t,Quintic.height Quintic.amplitude t))
  · right
    intro t
    have hneg : -euclideanCoordinates (t,Quintic.height Quintic.amplitude t) =
        euclideanCoordinates (-t,Quintic.height Quintic.amplitude (-t)) := by
      change -coordinateLinearEquiv _ = coordinateLinearEquiv _
      rw [←map_neg,Quintic.height_neg]
      rfl
    simpa only [IsometryEquiv.trans_apply,hneg,edgeChart_graph] using
      hs (euclideanCoordinates (t,Quintic.height Quintic.amplitude t))

end
end LiteralPlanar.Candidate
