module

public import SpectreFinite.ParentBoundaryFrameTable28
public import SpectreFinite.ParentBoundaryRow1278

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1278_states :
    FrameRows (indexedField parentRow1278) boundaryFrames28 := by decide

theorem boundaryFrameRow1278_structure :
    FramedRootStructure (indexedField parentRow1278) := by
  exact ⟨8,boundaryNeighbors11,boundaryFrames28,boundaryRow1278_shape,
    structure_of_table _ _ _ _ boundaryRow1278_sound
      boundaryTable11_covers boundaryTable11_structure,
    boundaryFrames28_geometry,boundaryFrameRow1278_states⟩

#print axioms boundaryFrameRow1278_structure
end SpectreFinite.HexSearch.ParentBoundary
