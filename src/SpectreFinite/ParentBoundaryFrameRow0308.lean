module

public import SpectreFinite.ParentBoundaryFrameTable15
public import SpectreFinite.ParentBoundaryRow0308

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0308_states :
    FrameRows (indexedField parentRow0308) boundaryFrames15 := by decide

theorem boundaryFrameRow0308_structure :
    FramedRootStructure (indexedField parentRow0308) := by
  exact ⟨0,boundaryNeighbors01,boundaryFrames15,boundaryRow0308_shape,
    structure_of_table _ _ _ _ boundaryRow0308_sound
      boundaryTable01_covers boundaryTable01_structure,
    boundaryFrames15_geometry,boundaryFrameRow0308_states⟩

#print axioms boundaryFrameRow0308_structure
end SpectreFinite.HexSearch.ParentBoundary
