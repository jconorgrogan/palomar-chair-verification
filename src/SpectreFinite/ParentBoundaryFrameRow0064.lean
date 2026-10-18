module

public import SpectreFinite.ParentBoundaryFrameTable00
public import SpectreFinite.ParentBoundaryRow0064

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0064_states :
    FrameRows (indexedField parentRow0064) boundaryFrames00 := by decide

theorem boundaryFrameRow0064_structure :
    FramedRootStructure (indexedField parentRow0064) := by
  exact ⟨6,boundaryNeighbors00,boundaryFrames00,boundaryRow0064_shape,
    structure_of_table _ _ _ _ boundaryRow0064_sound
      boundaryTable00_covers boundaryTable00_structure,
    boundaryFrames00_geometry,boundaryFrameRow0064_states⟩

#print axioms boundaryFrameRow0064_structure
end SpectreFinite.HexSearch.ParentBoundary
