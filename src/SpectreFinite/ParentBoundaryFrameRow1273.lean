module

public import SpectreFinite.ParentBoundaryFrameTable23
public import SpectreFinite.ParentBoundaryRow1273

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1273_states :
    FrameRows (indexedField parentRow1273) boundaryFrames23 := by decide

theorem boundaryFrameRow1273_structure :
    FramedRootStructure (indexedField parentRow1273) := by
  exact ⟨5,boundaryNeighbors09,boundaryFrames23,boundaryRow1273_shape,
    structure_of_table _ _ _ _ boundaryRow1273_sound
      boundaryTable09_covers boundaryTable09_structure,
    boundaryFrames23_geometry,boundaryFrameRow1273_states⟩

#print axioms boundaryFrameRow1273_structure
end SpectreFinite.HexSearch.ParentBoundary
