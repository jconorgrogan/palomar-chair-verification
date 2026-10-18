module

public import SpectreFinite.ParentBoundaryFrameTable39
public import SpectreFinite.ParentBoundaryRow1291

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1291_states :
    FrameRows (indexedField parentRow1291) boundaryFrames39 := by decide

theorem boundaryFrameRow1291_structure :
    FramedRootStructure (indexedField parentRow1291) := by
  exact ⟨1,boundaryNeighbors15,boundaryFrames39,boundaryRow1291_shape,
    structure_of_table _ _ _ _ boundaryRow1291_sound
      boundaryTable15_covers boundaryTable15_structure,
    boundaryFrames39_geometry,boundaryFrameRow1291_states⟩

#print axioms boundaryFrameRow1291_structure
end SpectreFinite.HexSearch.ParentBoundary
