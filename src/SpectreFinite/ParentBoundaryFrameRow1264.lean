module

public import SpectreFinite.ParentBoundaryFrameTable20
public import SpectreFinite.ParentBoundaryRow1264

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1264_states :
    FrameRows (indexedField parentRow1264) boundaryFrames20 := by decide

theorem boundaryFrameRow1264_structure :
    FramedRootStructure (indexedField parentRow1264) := by
  exact ⟨7,boundaryNeighbors07,boundaryFrames20,boundaryRow1264_shape,
    structure_of_table _ _ _ _ boundaryRow1264_sound
      boundaryTable07_covers boundaryTable07_structure,
    boundaryFrames20_geometry,boundaryFrameRow1264_states⟩

#print axioms boundaryFrameRow1264_structure
end SpectreFinite.HexSearch.ParentBoundary
