module

public import SpectreFinite.ParentBoundaryFrameTable37
public import SpectreFinite.ParentBoundaryRow1289

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1289_states :
    FrameRows (indexedField parentRow1289) boundaryFrames37 := by decide

theorem boundaryFrameRow1289_structure :
    FramedRootStructure (indexedField parentRow1289) := by
  exact ⟨1,boundaryNeighbors15,boundaryFrames37,boundaryRow1289_shape,
    structure_of_table _ _ _ _ boundaryRow1289_sound
      boundaryTable15_covers boundaryTable15_structure,
    boundaryFrames37_geometry,boundaryFrameRow1289_states⟩

#print axioms boundaryFrameRow1289_structure
end SpectreFinite.HexSearch.ParentBoundary
