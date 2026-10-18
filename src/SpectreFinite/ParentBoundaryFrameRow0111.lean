module

public import SpectreFinite.ParentBoundaryFrameTable13
public import SpectreFinite.ParentBoundaryRow0111

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0111_states :
    FrameRows (indexedField parentRow0111) boundaryFrames13 := by decide

theorem boundaryFrameRow0111_structure :
    FramedRootStructure (indexedField parentRow0111) := by
  exact ⟨4,boundaryNeighbors03,boundaryFrames13,boundaryRow0111_shape,
    structure_of_table _ _ _ _ boundaryRow0111_sound
      boundaryTable03_covers boundaryTable03_structure,
    boundaryFrames13_geometry,boundaryFrameRow0111_states⟩

#print axioms boundaryFrameRow0111_structure
end SpectreFinite.HexSearch.ParentBoundary
