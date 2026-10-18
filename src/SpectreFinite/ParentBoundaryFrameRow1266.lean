module

public import SpectreFinite.ParentBoundaryFrameTable22
public import SpectreFinite.ParentBoundaryRow1266

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1266_states :
    FrameRows (indexedField parentRow1266) boundaryFrames22 := by decide

theorem boundaryFrameRow1266_structure :
    FramedRootStructure (indexedField parentRow1266) := by
  exact ⟨2,boundaryNeighbors08,boundaryFrames22,boundaryRow1266_shape,
    structure_of_table _ _ _ _ boundaryRow1266_sound
      boundaryTable08_covers boundaryTable08_structure,
    boundaryFrames22_geometry,boundaryFrameRow1266_states⟩

#print axioms boundaryFrameRow1266_structure
end SpectreFinite.HexSearch.ParentBoundary
