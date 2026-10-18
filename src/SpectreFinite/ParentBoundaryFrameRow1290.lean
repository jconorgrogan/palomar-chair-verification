module

public import SpectreFinite.ParentBoundaryFrameTable38
public import SpectreFinite.ParentBoundaryRow1290

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1290_states :
    FrameRows (indexedField parentRow1290) boundaryFrames38 := by decide

theorem boundaryFrameRow1290_structure :
    FramedRootStructure (indexedField parentRow1290) := by
  exact ⟨1,boundaryNeighbors15,boundaryFrames38,boundaryRow1290_shape,
    structure_of_table _ _ _ _ boundaryRow1290_sound
      boundaryTable15_covers boundaryTable15_structure,
    boundaryFrames38_geometry,boundaryFrameRow1290_states⟩

#print axioms boundaryFrameRow1290_structure
end SpectreFinite.HexSearch.ParentBoundary
