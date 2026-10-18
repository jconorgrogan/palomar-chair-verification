module

public import SpectreFinite.ParentBoundaryFrameTable24
public import SpectreFinite.ParentBoundaryRow1274

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1274_states :
    FrameRows (indexedField parentRow1274) boundaryFrames24 := by decide

theorem boundaryFrameRow1274_structure :
    FramedRootStructure (indexedField parentRow1274) := by
  exact ⟨4,boundaryNeighbors10,boundaryFrames24,boundaryRow1274_shape,
    structure_of_table _ _ _ _ boundaryRow1274_sound
      boundaryTable10_covers boundaryTable10_structure,
    boundaryFrames24_geometry,boundaryFrameRow1274_states⟩

#print axioms boundaryFrameRow1274_structure
end SpectreFinite.HexSearch.ParentBoundary
