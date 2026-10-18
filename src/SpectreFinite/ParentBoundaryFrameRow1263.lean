module

public import SpectreFinite.ParentBoundaryFrameTable19
public import SpectreFinite.ParentBoundaryRow1263

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1263_states :
    FrameRows (indexedField parentRow1263) boundaryFrames19 := by decide

theorem boundaryFrameRow1263_structure :
    FramedRootStructure (indexedField parentRow1263) := by
  exact ⟨7,boundaryNeighbors07,boundaryFrames19,boundaryRow1263_shape,
    structure_of_table _ _ _ _ boundaryRow1263_sound
      boundaryTable07_covers boundaryTable07_structure,
    boundaryFrames19_geometry,boundaryFrameRow1263_states⟩

#print axioms boundaryFrameRow1263_structure
end SpectreFinite.HexSearch.ParentBoundary
