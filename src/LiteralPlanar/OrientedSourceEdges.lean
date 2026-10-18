module

public import SpectreGeometry.PhysicalEdgeOrientation

@[expose] public section


/-! A registered reversed partner for every source unit edge, derived from
an explicit proper whole-plane P tiling. No existence assertion is hidden. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry

theorem homochiral_source_edges_have_reversed_partner {I : Type*}
    (p : I → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (p i))
    (hcover : ∀ x, ∃ i, x ∈ p i '' euclideanBody)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (p i '' euclideanBody)) (interior (p j '' euclideanBody)))
    (root : I) (e : Fin 14) :
    ∃ i, i ≠ root ∧ ∃ j : Fin 14,
      p root (euclideanVertex e) = p i (euclideanVertex (next j)) ∧
      p root (euclideanVertex (next e)) = p i (euclideanVertex j) := by
  obtain ⟨i,hi,j,hmatch⟩ :=
    homochiral_whole_unit_edge_registration p hdirect hdisjoint hcover root e
  refine ⟨i,hi,j,?_⟩
  rcases hmatch with ⟨ha,hb⟩ | hrev
  · let x := p root (euclideanCoordinates
      (interpolate (realVertex e) (realVertex (next e)) (1 / 2)))
    have hxj : x = p i (euclideanCoordinates
        (interpolate (realVertex j) (realVertex (next j)) (1 / 2))) := by
      dsimp [x]
      rw [placed_edge_interpolate, placed_edge_interpolate]
      simp only [placedEdgeVector, ←ha, ←hb]
    exact homochiral_contact_unit_edges_reversed p hdirect hdisjoint hcover root i hi e j
      (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      x rfl hxj
  · exact hrev

end
end LiteralPlanar.Forward
