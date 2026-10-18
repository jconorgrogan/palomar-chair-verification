module

public import SpectreFinite.ParentBoundaryFrameTable21
public import SpectreFinite.ParentBoundaryRow1265

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1265_states :
    FrameRows (indexedField parentRow1265) boundaryFrames21 := by decide

theorem boundaryFrameRow1265_structure :
    FramedRootStructure (indexedField parentRow1265) := by
  exact ⟨7,boundaryNeighbors06,boundaryFrames21,boundaryRow1265_shape,
    structure_of_table _ _ _ _ boundaryRow1265_sound
      boundaryTable06_covers boundaryTable06_structure,
    boundaryFrames21_geometry,boundaryFrameRow1265_states⟩

#print axioms boundaryFrameRow1265_structure
end SpectreFinite.HexSearch.ParentBoundary
