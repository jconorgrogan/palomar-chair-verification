module

public import SpectreFinite.ParentBoundaryFrameTable33
public import SpectreFinite.ParentBoundaryRow1283

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1283_states :
    FrameRows (indexedField parentRow1283) boundaryFrames33 := by decide

theorem boundaryFrameRow1283_structure :
    FramedRootStructure (indexedField parentRow1283) := by
  exact ⟨7,boundaryNeighbors14,boundaryFrames33,boundaryRow1283_shape,
    structure_of_table _ _ _ _ boundaryRow1283_sound
      boundaryTable14_covers boundaryTable14_structure,
    boundaryFrames33_geometry,boundaryFrameRow1283_states⟩

#print axioms boundaryFrameRow1283_structure
end SpectreFinite.HexSearch.ParentBoundary
