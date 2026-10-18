module

public import SpectreFinite.ParentBoundaryFrameTable02
public import SpectreFinite.ParentBoundaryRow0070

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0070_states :
    FrameRows (indexedField parentRow0070) boundaryFrames02 := by decide

theorem boundaryFrameRow0070_structure :
    FramedRootStructure (indexedField parentRow0070) := by
  exact ⟨6,boundaryNeighbors00,boundaryFrames02,boundaryRow0070_shape,
    structure_of_table _ _ _ _ boundaryRow0070_sound
      boundaryTable00_covers boundaryTable00_structure,
    boundaryFrames02_geometry,boundaryFrameRow0070_states⟩

#print axioms boundaryFrameRow0070_structure
end SpectreFinite.HexSearch.ParentBoundary
