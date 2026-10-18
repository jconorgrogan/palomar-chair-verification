module

public import SpectreFinite.ParentBoundaryFrameTable17
public import SpectreFinite.ParentBoundaryRow0514

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0514_states :
    FrameRows (indexedField parentRow0514) boundaryFrames17 := by decide

theorem boundaryFrameRow0514_structure :
    FramedRootStructure (indexedField parentRow0514) := by
  exact ⟨5,boundaryNeighbors02,boundaryFrames17,boundaryRow0514_shape,
    structure_of_table _ _ _ _ boundaryRow0514_sound
      boundaryTable02_covers boundaryTable02_structure,
    boundaryFrames17_geometry,boundaryFrameRow0514_states⟩

#print axioms boundaryFrameRow0514_structure
end SpectreFinite.HexSearch.ParentBoundary
