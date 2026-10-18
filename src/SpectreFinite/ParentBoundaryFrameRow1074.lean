module

public import SpectreFinite.ParentBoundaryFrameTable16
public import SpectreFinite.ParentBoundaryRow1074

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1074_states :
    FrameRows (indexedField parentRow1074) boundaryFrames16 := by decide

theorem boundaryFrameRow1074_structure :
    FramedRootStructure (indexedField parentRow1074) := by
  exact ⟨0,boundaryNeighbors01,boundaryFrames16,boundaryRow1074_shape,
    structure_of_table _ _ _ _ boundaryRow1074_sound
      boundaryTable01_covers boundaryTable01_structure,
    boundaryFrames16_geometry,boundaryFrameRow1074_states⟩

#print axioms boundaryFrameRow1074_structure
end SpectreFinite.HexSearch.ParentBoundary
