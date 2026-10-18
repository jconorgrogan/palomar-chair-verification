module

public import SpectreFinite.ParentBoundaryFrameTable27
public import SpectreFinite.ParentBoundaryRow1277

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1277_states :
    FrameRows (indexedField parentRow1277) boundaryFrames27 := by decide

theorem boundaryFrameRow1277_structure :
    FramedRootStructure (indexedField parentRow1277) := by
  exact ⟨8,boundaryNeighbors11,boundaryFrames27,boundaryRow1277_shape,
    structure_of_table _ _ _ _ boundaryRow1277_sound
      boundaryTable11_covers boundaryTable11_structure,
    boundaryFrames27_geometry,boundaryFrameRow1277_states⟩

#print axioms boundaryFrameRow1277_structure
end SpectreFinite.HexSearch.ParentBoundary
