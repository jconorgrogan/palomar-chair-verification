module

public import SpectreFinite.ParentBoundaryFrameTable16
public import SpectreFinite.ParentBoundaryRow0309

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0309_states :
    FrameRows (indexedField parentRow0309) boundaryFrames16 := by decide

theorem boundaryFrameRow0309_structure :
    FramedRootStructure (indexedField parentRow0309) := by
  exact ⟨0,boundaryNeighbors01,boundaryFrames16,boundaryRow0309_shape,
    structure_of_table _ _ _ _ boundaryRow0309_sound
      boundaryTable01_covers boundaryTable01_structure,
    boundaryFrames16_geometry,boundaryFrameRow0309_states⟩

#print axioms boundaryFrameRow0309_structure
end SpectreFinite.HexSearch.ParentBoundary
