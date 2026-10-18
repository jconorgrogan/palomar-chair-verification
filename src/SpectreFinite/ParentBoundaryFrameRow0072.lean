module

public import SpectreFinite.ParentBoundaryFrameTable04
public import SpectreFinite.ParentBoundaryRow0072

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0072_states :
    FrameRows (indexedField parentRow0072) boundaryFrames04 := by decide

theorem boundaryFrameRow0072_structure :
    FramedRootStructure (indexedField parentRow0072) := by
  exact ⟨6,boundaryNeighbors00,boundaryFrames04,boundaryRow0072_shape,
    structure_of_table _ _ _ _ boundaryRow0072_sound
      boundaryTable00_covers boundaryTable00_structure,
    boundaryFrames04_geometry,boundaryFrameRow0072_states⟩

#print axioms boundaryFrameRow0072_structure
end SpectreFinite.HexSearch.ParentBoundary
