module

public import SpectreFinite.ParentBoundaryFrameTable25
public import SpectreFinite.ParentBoundaryRow1275

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1275_states :
    FrameRows (indexedField parentRow1275) boundaryFrames25 := by decide

theorem boundaryFrameRow1275_structure :
    FramedRootStructure (indexedField parentRow1275) := by
  exact ⟨8,boundaryNeighbors11,boundaryFrames25,boundaryRow1275_shape,
    structure_of_table _ _ _ _ boundaryRow1275_sound
      boundaryTable11_covers boundaryTable11_structure,
    boundaryFrames25_geometry,boundaryFrameRow1275_states⟩

#print axioms boundaryFrameRow1275_structure
end SpectreFinite.HexSearch.ParentBoundary
