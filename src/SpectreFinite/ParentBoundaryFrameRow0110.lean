module

public import SpectreFinite.ParentBoundaryFrameTable13
public import SpectreFinite.ParentBoundaryRow0110

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0110_states :
    FrameRows (indexedField parentRow0110) boundaryFrames13 := by decide

theorem boundaryFrameRow0110_structure :
    FramedRootStructure (indexedField parentRow0110) := by
  exact ⟨4,boundaryNeighbors03,boundaryFrames13,boundaryRow0110_shape,
    structure_of_table _ _ _ _ boundaryRow0110_sound
      boundaryTable03_covers boundaryTable03_structure,
    boundaryFrames13_geometry,boundaryFrameRow0110_states⟩

#print axioms boundaryFrameRow0110_structure
end SpectreFinite.HexSearch.ParentBoundary
