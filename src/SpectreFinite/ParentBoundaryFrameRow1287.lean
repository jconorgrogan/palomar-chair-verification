module

public import SpectreFinite.ParentBoundaryFrameTable36
public import SpectreFinite.ParentBoundaryRow1287

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1287_states :
    FrameRows (indexedField parentRow1287) boundaryFrames36 := by decide

theorem boundaryFrameRow1287_structure :
    FramedRootStructure (indexedField parentRow1287) := by
  exact ⟨1,boundaryNeighbors16,boundaryFrames36,boundaryRow1287_shape,
    structure_of_table _ _ _ _ boundaryRow1287_sound
      boundaryTable16_covers boundaryTable16_structure,
    boundaryFrames36_geometry,boundaryFrameRow1287_states⟩

#print axioms boundaryFrameRow1287_structure
end SpectreFinite.HexSearch.ParentBoundary
