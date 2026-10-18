module

public import SpectreFinite.ParentBoundaryFrameTable26
public import SpectreFinite.ParentBoundaryRow1276

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1276_states :
    FrameRows (indexedField parentRow1276) boundaryFrames26 := by decide

theorem boundaryFrameRow1276_structure :
    FramedRootStructure (indexedField parentRow1276) := by
  exact ⟨8,boundaryNeighbors11,boundaryFrames26,boundaryRow1276_shape,
    structure_of_table _ _ _ _ boundaryRow1276_sound
      boundaryTable11_covers boundaryTable11_structure,
    boundaryFrames26_geometry,boundaryFrameRow1276_states⟩

#print axioms boundaryFrameRow1276_structure
end SpectreFinite.HexSearch.ParentBoundary
