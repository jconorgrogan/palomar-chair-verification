module

public import SpectreFinite.ParentBoundaryFrameTable18
public import SpectreFinite.ParentBoundaryRow1262

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1262_states :
    FrameRows (indexedField parentRow1262) boundaryFrames18 := by decide

theorem boundaryFrameRow1262_structure :
    FramedRootStructure (indexedField parentRow1262) := by
  exact ⟨7,boundaryNeighbors06,boundaryFrames18,boundaryRow1262_shape,
    structure_of_table _ _ _ _ boundaryRow1262_sound
      boundaryTable06_covers boundaryTable06_structure,
    boundaryFrames18_geometry,boundaryFrameRow1262_states⟩

#print axioms boundaryFrameRow1262_structure
end SpectreFinite.HexSearch.ParentBoundary
