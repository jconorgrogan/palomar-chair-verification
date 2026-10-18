module

public import SpectreFinite.ParentBoundaryFrameTable09
public import SpectreFinite.ParentBoundaryRow0106

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0106_states :
    FrameRows (indexedField parentRow0106) boundaryFrames09 := by decide

theorem boundaryFrameRow0106_structure :
    FramedRootStructure (indexedField parentRow0106) := by
  exact ⟨8,boundaryNeighbors04,boundaryFrames09,boundaryRow0106_shape,
    structure_of_table _ _ _ _ boundaryRow0106_sound
      boundaryTable04_covers boundaryTable04_structure,
    boundaryFrames09_geometry,boundaryFrameRow0106_states⟩

#print axioms boundaryFrameRow0106_structure
end SpectreFinite.HexSearch.ParentBoundary
