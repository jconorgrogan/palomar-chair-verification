module

public import SpectreFinite.ParentBoundaryFrameTable31
public import SpectreFinite.ParentBoundaryRow1281

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1281_states :
    FrameRows (indexedField parentRow1281) boundaryFrames31 := by decide

theorem boundaryFrameRow1281_structure :
    FramedRootStructure (indexedField parentRow1281) := by
  exact ⟨7,boundaryNeighbors13,boundaryFrames31,boundaryRow1281_shape,
    structure_of_table _ _ _ _ boundaryRow1281_sound
      boundaryTable13_covers boundaryTable13_structure,
    boundaryFrames31_geometry,boundaryFrameRow1281_states⟩

#print axioms boundaryFrameRow1281_structure
end SpectreFinite.HexSearch.ParentBoundary
