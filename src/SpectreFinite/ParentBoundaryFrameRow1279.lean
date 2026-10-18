module

public import SpectreFinite.ParentBoundaryFrameTable29
public import SpectreFinite.ParentBoundaryRow1279

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1279_states :
    FrameRows (indexedField parentRow1279) boundaryFrames29 := by decide

theorem boundaryFrameRow1279_structure :
    FramedRootStructure (indexedField parentRow1279) := by
  exact ⟨4,boundaryNeighbors10,boundaryFrames29,boundaryRow1279_shape,
    structure_of_table _ _ _ _ boundaryRow1279_sound
      boundaryTable10_covers boundaryTable10_structure,
    boundaryFrames29_geometry,boundaryFrameRow1279_states⟩

#print axioms boundaryFrameRow1279_structure
end SpectreFinite.HexSearch.ParentBoundary
