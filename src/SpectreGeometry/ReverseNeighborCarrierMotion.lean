module

public import SpectreGeometry.ReversePlacedClusterCharts
public import SpectreGeometry.ReverseClusterNeighborCellsReal

@[expose] public section


namespace SpectreGeometry.ReverseClusterNeighborCells
noncomputable section
open Set SpectreClusters SpectreFinite.HexSearch ReverseClusterTriangulation ReverseExistence

theorem neighborCarrier_eq_motion_image (c : Configuration) :
    neighborCarrier c =
      gridMotion c.turn (integerPoint (lattice c.centerShift)) '' rawClusterBody c.neighborKind := by
  have hcell (a : Cell) : gridKiteBody (moveCell c.turn c.centerShift a) =
      gridMotion c.turn (integerPoint (lattice c.centerShift)) '' gridKiteBody a := by
    rw [gridKiteBody,cellVertices_moved,integerHull_image_motion]
    rfl
  ext x
  constructor
  · intro hx
    obtain ⟨b,hb,hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    rw [hcell] at hx
    obtain ⟨q,hq,rfl⟩ := hx
    exact ⟨q,mem_iUnion₂.mpr ⟨a,ha,hq⟩,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨a,ha,hq⟩ := mem_iUnion₂.mp hq
    apply mem_iUnion₂.mpr
    refine ⟨moveCell c.turn c.centerShift a,List.mem_map.mpr ⟨a,ha,rfl⟩,?_⟩
    rw [hcell]
    exact ⟨q,hq,rfl⟩

theorem gridRotation_compose (r s : Fin 6) (p : RealPoint) :
    gridRotation r (gridRotation s p) = gridRotation (rotateTurn r s) p := by
  fin_cases r <;> fin_cases s <;> ext <;> simp [gridRotation,rotateTurn] <;> ring

theorem axialMotionHomeomorph_gridMotion (r s : Fin 6) (a b p : RealPoint) :
    axialMotionHomeomorph r a (gridMotion s b p) =
      a+gridRotation r b+gridRotation (rotateTurn r s) p := by
  change a+gridRotationLinear r (b+gridRotation s p) = _
  rw [map_add]
  change a+(gridRotation r b+gridRotation r (gridRotation s p)) = _
  rw [gridRotation_compose]
  abel

end
end SpectreGeometry.ReverseClusterNeighborCells
