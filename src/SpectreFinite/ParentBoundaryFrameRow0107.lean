module

public import SpectreFinite.ParentBoundaryFrameTable10
public import SpectreFinite.ParentBoundaryRow0107

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0107_states :
    FrameRows (indexedField parentRow0107) boundaryFrames10 := by decide

theorem boundaryFrameRow0107_structure :
    FramedRootStructure (indexedField parentRow0107) := by
  exact ⟨8,boundaryNeighbors04,boundaryFrames10,boundaryRow0107_shape,
    structure_of_table _ _ _ _ boundaryRow0107_sound
      boundaryTable04_covers boundaryTable04_structure,
    boundaryFrames10_geometry,boundaryFrameRow0107_states⟩

#print axioms boundaryFrameRow0107_structure
end SpectreFinite.HexSearch.ParentBoundary
