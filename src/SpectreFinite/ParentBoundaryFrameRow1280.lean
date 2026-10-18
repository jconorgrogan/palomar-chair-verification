module

public import SpectreFinite.ParentBoundaryFrameTable30
public import SpectreFinite.ParentBoundaryRow1280

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1280_states :
    FrameRows (indexedField parentRow1280) boundaryFrames30 := by decide

theorem boundaryFrameRow1280_structure :
    FramedRootStructure (indexedField parentRow1280) := by
  exact ⟨3,boundaryNeighbors12,boundaryFrames30,boundaryRow1280_shape,
    structure_of_table _ _ _ _ boundaryRow1280_sound
      boundaryTable12_covers boundaryTable12_structure,
    boundaryFrames30_geometry,boundaryFrameRow1280_states⟩

#print axioms boundaryFrameRow1280_structure
end SpectreFinite.HexSearch.ParentBoundary
