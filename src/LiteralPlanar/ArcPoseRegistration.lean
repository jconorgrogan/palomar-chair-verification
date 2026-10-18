module

public import LiteralPlanar.WholeArcRegistration

@[expose] public section


/-! Infinite contact also determines the entire relative Euclidean pose of
canonical arcs. Endpoint registration therefore retains the collinear midpoint. -/
namespace LiteralPlanar.Quintic
noncomputable section
open SpectreGeometry

theorem graph_symmetry_full_isometry (f : EPlane ≃ᵢ EPlane)
    (hf : IsGraphSymmetry (isometryCoefficients f)) :
    (∀ x : EPlane, f x = x) ∨ (∀ x : EPlane, f x = -x) := by
  rcases hf with ⟨hb,hc,hu,hv,⟨ha,hd⟩ | ⟨ha,hd⟩⟩
  · left
    intro x
    obtain ⟨p,rfl⟩ := euclideanCoordinates.surjective x
    apply euclideanCoordinates.symm.injective
    rw [isometry_coefficients_apply,Homeomorph.symm_apply_apply]
    simp only [ha,hb,hc,hd,hu,hv,one_mul,zero_mul,add_zero,zero_add]
  · right
    intro x
    obtain ⟨p,rfl⟩ := euclideanCoordinates.surjective x
    apply euclideanCoordinates.symm.injective
    rw [isometry_coefficients_apply]
    have he : euclideanCoordinates.symm (-euclideanCoordinates p) = -p := by
      change coordinateLinearEquiv.symm (-coordinateLinearEquiv p) = -p
      rw [map_neg,coordinateLinearEquiv.symm_apply_apply]
    rw [he]
    simp only [ha,hb,hc,hd,hu,hv,neg_one_mul,zero_mul,add_zero,zero_add]
    apply Prod.ext <;> rfl

theorem infinite_placed_standardArcs_pose (ε : ℝ) (hε : ε ≠ 0)
    (f g : EPlane ≃ᵢ EPlane)
    (h : (f '' standardArc ε ∩ g '' standardArc ε).Infinite) :
    (∀ x : EPlane, f x = g x) ∨ (∀ x : EPlane, f x = g (-x)) := by
  have hi : ((f.trans g.symm) '' standardArc ε ∩ standardArc ε).Infinite := by
    rw [←inverse_image_inter]
    exact h.image g.symm.injective.injOn
  rcases graph_symmetry_full_isometry (f.trans g.symm)
      (infinite_standardArc_contact_rigidity ε hε _ hi) with hs | hs
  · left
    intro x
    have he := congrArg g (hs x)
    simpa only [IsometryEquiv.trans_apply,IsometryEquiv.apply_symm_apply] using he
  · right
    intro x
    have he := congrArg g (hs x)
    simpa only [IsometryEquiv.trans_apply,IsometryEquiv.apply_symm_apply] using he

end
end LiteralPlanar.Quintic

namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry

theorem edgeChart_left (e : Fin 14) :
    edgeChart e (euclideanCoordinates ((-1/2 : ℝ),0)) = euclideanVertex e := by
  have h := edgeChart_graph e (-1/2)
  rw [Quintic.height_left] at h
  simpa only [edgeCurve,Quintic.height_left,show (-1/2 : ℝ)+1/2=0 by norm_num,zero_smul,add_zero,euclideanVertex] using h

theorem edgeChart_right (e : Fin 14) :
    edgeChart e (euclideanCoordinates ((1/2 : ℝ),0)) = euclideanVertex (next e) := by
  have h := edgeChart_graph e (1/2)
  rw [Quintic.height_right] at h
  have he : (1/2 : ℝ)+1/2=1 := by norm_num
  simp only [edgeCurve,Quintic.height_right,he,zero_smul,one_smul,add_zero] at h
  have hh : realVertex e + realEdge e = realVertex (next e) := by
    change realVertex e + (realVertex (next e)-realVertex e) = _
    abel
  simpa only [hh,euclideanVertex] using h

theorem infinite_placed_edgeArcs_endpoints (f g : EPlane ≃ᵢ EPlane)
    (e j : Fin 14) (h : (f '' euclideanArc e ∩ g '' euclideanArc j).Infinite) :
    (f (euclideanVertex e) = g (euclideanVertex j) ∧
      f (euclideanVertex (next e)) = g (euclideanVertex (next j))) ∨
    (f (euclideanVertex e) = g (euclideanVertex (next j)) ∧
      f (euclideanVertex (next e)) = g (euclideanVertex j)) := by
  have himage (q : EPlane ≃ᵢ EPlane) (k : Fin 14) :
      q '' euclideanArc k = (edgeChart k |>.trans q) '' Quintic.standardArc Quintic.amplitude := by
    rw [euclideanArc_eq_chart_image,Set.image_image]
    rfl
  rw [himage,himage] at h
  rcases Quintic.infinite_placed_standardArcs_pose Quintic.amplitude
      (by norm_num [Quintic.amplitude]) _ _ h with hs | hs
  · left
    constructor
    · simpa only [IsometryEquiv.trans_apply,edgeChart_left] using
        hs (euclideanCoordinates ((-1/2 : ℝ),0))
    · simpa only [IsometryEquiv.trans_apply,edgeChart_right] using
        hs (euclideanCoordinates ((1/2 : ℝ),0))
  · have negleft : -euclideanCoordinates ((-1/2 : ℝ),0) = euclideanCoordinates ((1/2 : ℝ),0) := by
      change -coordinateLinearEquiv _ = coordinateLinearEquiv _
      rw [←map_neg]
      congr 1 <;> norm_num
    have negright : -euclideanCoordinates ((1/2 : ℝ),0) = euclideanCoordinates ((-1/2 : ℝ),0) := by
      rw [←negleft,neg_neg]
    right
    constructor
    · simpa only [IsometryEquiv.trans_apply,negleft,edgeChart_left,edgeChart_right] using
        hs (euclideanCoordinates ((-1/2 : ℝ),0))
    · simpa only [IsometryEquiv.trans_apply,negright,edgeChart_left,edgeChart_right] using
        hs (euclideanCoordinates ((1/2 : ℝ),0))

end
end LiteralPlanar.Candidate
