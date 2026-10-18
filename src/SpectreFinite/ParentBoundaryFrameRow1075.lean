module

public import SpectreFinite.ParentBoundaryFrameTable16
public import SpectreFinite.ParentBoundaryRow1075

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1075_states :
    FrameRows (indexedField parentRow1075) boundaryFrames16 := by decide

theorem boundaryFrameRow1075_structure :
    FramedRootStructure (indexedField parentRow1075) := by
  exact ⟨0,boundaryNeighbors01,boundaryFrames16,boundaryRow1075_shape,
    structure_of_table _ _ _ _ boundaryRow1075_sound
      boundaryTable01_covers boundaryTable01_structure,
    boundaryFrames16_geometry,boundaryFrameRow1075_states⟩

#print axioms boundaryFrameRow1075_structure
end SpectreFinite.HexSearch.ParentBoundary
