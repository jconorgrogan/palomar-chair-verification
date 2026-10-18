module

public import LiteralPlanar.TileResidual
public import LiteralPlanar.LiteralCandidate

@[expose] public section


/-! Exact image identification for the literal polynomial body. This does not
assert that tileMap is globally injective or a homeomorphism. -/
namespace LiteralPlanar.FanBounds
noncomputable section
open SpectreGeometry

def tileMap (x : EPlane) : EPlane := x + tileResidual x

def curvedBody : Set EPlane := euclideanCoordinates '' Candidate.body

theorem centers_agree : center = Candidate.center := by
  norm_num [center, Candidate.center, fanCenter, realize, Quad3.eval]

theorem affineFan_mem_triangleBody (i : Fin 14) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a + b ≤ 1) :
    affineFan i a b ∈ triangleBody i := by
  rw [←sourceDomain_eq_triangleBody]
  change 0 ≤ alpha i (affineFan i a b) ∧ 0 ≤ beta i (affineFan i a b) ∧
    alpha i (affineFan i a b) + beta i (affineFan i a b) ≤ 1
  rw [alpha_affineFan, beta_affineFan]
  exact ⟨ha,hb,hs⟩

theorem tileMap_affineFan (i : Fin 14) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a + b ≤ 1) :
    tileMap (euclideanCoordinates (affineFan i a b)) =
      euclideanCoordinates (Candidate.fanPatch i (a,b)) := by
  have hp := affineFan_mem_triangleBody i a b ha hb hs
  rw [tileMap, tileResidual_on_fan i _ (by simpa only [Homeomorph.symm_apply_apply] using hp)]
  simp only [residual, Homeomorph.symm_apply_apply, alpha_affineFan, beta_affineFan, normal]
  change coordinateLinearEquiv (affineFan i a b) +
      Quintic.fanHeight Quintic.amplitude a b • coordinateLinearEquiv (quarterTurn (realEdge i)) =
    coordinateLinearEquiv (Candidate.fanPatch i (a,b))
  rw [←map_smul, ←map_add]
  congr 1
  simp only [Candidate.fanPatch, affineFan, radial, centers_agree]
  rfl

/-- The selected-fan map sends exactly the original P carrier onto the literal
finite union of polynomial simplex images. Homeomorphism is still separate. -/
theorem tileMap_image_body : tileMap '' euclideanBody = curvedBody := by
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    obtain ⟨p,hp,rfl⟩ := hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    have hc : p ∈ sourceDomain i := by rwa [sourceDomain_eq_triangleBody]
    obtain ⟨ha,hb,hs⟩ := hc
    refine ⟨Candidate.fanPatch i (alpha i p, beta i p),?_,?_⟩
    · exact Set.mem_iUnion.mpr ⟨i,⟨(alpha i p,beta i p),⟨ha,hb,hs⟩,rfl⟩⟩
    · simpa only [affineFan_reconstruct] using
        (tileMap_affineFan i (alpha i p) (beta i p) ha hb hs).symm
  · rintro y ⟨z,hz,rfl⟩
    obtain ⟨i,w,hw,rfl⟩ := Set.mem_iUnion.mp hz
    obtain ⟨ha,hb,hs⟩ := hw
    refine ⟨euclideanCoordinates (affineFan i w.1 w.2),?_,?_⟩
    · exact ⟨affineFan i w.1 w.2,
        Set.mem_iUnion.mpr ⟨i,affineFan_mem_triangleBody i w.1 w.2 ha hb hs⟩,rfl⟩
    · exact tileMap_affineFan i w.1 w.2 ha hb hs

end
end LiteralPlanar.FanBounds
