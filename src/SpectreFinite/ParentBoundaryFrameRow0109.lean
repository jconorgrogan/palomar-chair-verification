module

public import SpectreFinite.ParentBoundaryFrameTable12
public import SpectreFinite.ParentBoundaryRow0109

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0109_states :
    FrameRows (indexedField parentRow0109) boundaryFrames12 := by decide

theorem boundaryFrameRow0109_structure :
    FramedRootStructure (indexedField parentRow0109) := by
  exact ⟨5,boundaryNeighbors02,boundaryFrames12,boundaryRow0109_shape,
    structure_of_table _ _ _ _ boundaryRow0109_sound
      boundaryTable02_covers boundaryTable02_structure,
    boundaryFrames12_geometry,boundaryFrameRow0109_states⟩

#print axioms boundaryFrameRow0109_structure
end SpectreFinite.HexSearch.ParentBoundary
