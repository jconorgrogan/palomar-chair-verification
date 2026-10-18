module

public import SpectreFinite.ParentBoundaryFrameTable03
public import SpectreFinite.ParentBoundaryRow0071

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0071_states :
    FrameRows (indexedField parentRow0071) boundaryFrames03 := by decide

theorem boundaryFrameRow0071_structure :
    FramedRootStructure (indexedField parentRow0071) := by
  exact ⟨6,boundaryNeighbors00,boundaryFrames03,boundaryRow0071_shape,
    structure_of_table _ _ _ _ boundaryRow0071_sound
      boundaryTable00_covers boundaryTable00_structure,
    boundaryFrames03_geometry,boundaryFrameRow0071_states⟩

#print axioms boundaryFrameRow0071_structure
end SpectreFinite.HexSearch.ParentBoundary
