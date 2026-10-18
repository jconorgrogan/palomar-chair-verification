module

public import SpectreFinite.ParentBoundaryFrameTable01
public import SpectreFinite.ParentBoundaryRow0065

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0065_states :
    FrameRows (indexedField parentRow0065) boundaryFrames01 := by decide

theorem boundaryFrameRow0065_structure :
    FramedRootStructure (indexedField parentRow0065) := by
  exact ⟨6,boundaryNeighbors00,boundaryFrames01,boundaryRow0065_shape,
    structure_of_table _ _ _ _ boundaryRow0065_sound
      boundaryTable00_covers boundaryTable00_structure,
    boundaryFrames01_geometry,boundaryFrameRow0065_states⟩

#print axioms boundaryFrameRow0065_structure
end SpectreFinite.HexSearch.ParentBoundary
