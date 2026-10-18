module

public import LiteralPlanar.EdgeArcCharts

@[expose] public section


/-! Infinite set contact forces an entire arc mate. This does not yet exclude
additional point contacts or identify an arbitrary physical body's frontier. -/
namespace LiteralPlanar.Quintic
noncomputable section
open SpectreGeometry

theorem inverse_image_inter (A : Set EPlane) (f g : EPlane ≃ᵢ EPlane) :
    g.symm '' (f '' A ∩ g '' A) = (f.trans g.symm) '' A ∩ A := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,⟨⟨a,ha,rfl⟩,⟨b,hb,hb'⟩⟩,rfl⟩
    constructor
    · exact ⟨a,ha,rfl⟩
    · rw [←hb',IsometryEquiv.symm_apply_apply]
      exact hb
  · rintro x ⟨⟨a,ha,rfl⟩,hb⟩
    refine ⟨f a,⟨⟨a,ha,rfl⟩,?_⟩,rfl⟩
    exact ⟨g.symm (f a),hb,g.apply_symm_apply _⟩

theorem infinite_placed_standardArcs_whole (ε : ℝ) (hε : ε ≠ 0)
    (f g : EPlane ≃ᵢ EPlane)
    (h : (f '' standardArc ε ∩ g '' standardArc ε).Infinite) :
    f '' standardArc ε = g '' standardArc ε := by
  have hi : ((f.trans g.symm) '' standardArc ε ∩ standardArc ε).Infinite := by
    rw [←inverse_image_inter]
    exact h.image g.symm.injective.injOn
  have hs := infinite_standardArc_contact_rigidity ε hε (f.trans g.symm) hi
  have he := graph_symmetry_arc_image ε (f.trans g.symm) hs
  apply Set.Subset.antisymm
  · rintro x ⟨a,ha,rfl⟩
    refine ⟨g.symm (f a),?_,g.apply_symm_apply _⟩
    rw [←he]
    exact ⟨a,ha,rfl⟩
  · rintro x ⟨a,ha,rfl⟩
    rw [←he] at ha
    obtain ⟨b,hb,hba⟩ := ha
    refine ⟨b,hb,?_⟩
    have hh := congrArg g hba
    simpa only [IsometryEquiv.trans_apply,IsometryEquiv.apply_symm_apply] using hh

end
end LiteralPlanar.Quintic

namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry

theorem infinite_placed_edgeArcs_whole (f g : EPlane ≃ᵢ EPlane)
    (e j : Fin 14) (h : (f '' euclideanArc e ∩ g '' euclideanArc j).Infinite) :
    f '' euclideanArc e = g '' euclideanArc j := by
  have himage (q : EPlane ≃ᵢ EPlane) (k : Fin 14) :
      q '' euclideanArc k = (edgeChart k |>.trans q) '' Quintic.standardArc Quintic.amplitude := by
    rw [euclideanArc_eq_chart_image,Set.image_image]
    rfl
  rw [himage,himage] at h ⊢
  exact Quintic.infinite_placed_standardArcs_whole Quintic.amplitude (by norm_num [Quintic.amplitude]) _ _ h

end
end LiteralPlanar.Candidate
