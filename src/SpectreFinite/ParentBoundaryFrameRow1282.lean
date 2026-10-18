module

public import SpectreFinite.ParentBoundaryFrameTable32
public import SpectreFinite.ParentBoundaryRow1282

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1282_states :
    FrameRows (indexedField parentRow1282) boundaryFrames32 := by decide

theorem boundaryFrameRow1282_structure :
    FramedRootStructure (indexedField parentRow1282) := by
  exact ⟨7,boundaryNeighbors14,boundaryFrames32,boundaryRow1282_shape,
    structure_of_table _ _ _ _ boundaryRow1282_sound
      boundaryTable14_covers boundaryTable14_structure,
    boundaryFrames32_geometry,boundaryFrameRow1282_states⟩

#print axioms boundaryFrameRow1282_structure
end SpectreFinite.HexSearch.ParentBoundary
