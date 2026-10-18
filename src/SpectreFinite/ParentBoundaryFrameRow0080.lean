module

public import SpectreFinite.ParentBoundaryFrameTable05
public import SpectreFinite.ParentBoundaryRow0080

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0080_states :
    FrameRows (indexedField parentRow0080) boundaryFrames05 := by decide

theorem boundaryFrameRow0080_structure :
    FramedRootStructure (indexedField parentRow0080) := by
  exact ⟨0,boundaryNeighbors01,boundaryFrames05,boundaryRow0080_shape,
    structure_of_table _ _ _ _ boundaryRow0080_sound
      boundaryTable01_covers boundaryTable01_structure,
    boundaryFrames05_geometry,boundaryFrameRow0080_states⟩

#print axioms boundaryFrameRow0080_structure
end SpectreFinite.HexSearch.ParentBoundary
