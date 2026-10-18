module

public import SpectreFinite.ParentBoundaryFrameTable35
public import SpectreFinite.ParentBoundaryRow1285

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1285_states :
    FrameRows (indexedField parentRow1285) boundaryFrames35 := by decide

theorem boundaryFrameRow1285_structure :
    FramedRootStructure (indexedField parentRow1285) := by
  exact ⟨1,boundaryNeighbors15,boundaryFrames35,boundaryRow1285_shape,
    structure_of_table _ _ _ _ boundaryRow1285_sound
      boundaryTable15_covers boundaryTable15_structure,
    boundaryFrames35_geometry,boundaryFrameRow1285_states⟩

#print axioms boundaryFrameRow1285_structure
end SpectreFinite.HexSearch.ParentBoundary
