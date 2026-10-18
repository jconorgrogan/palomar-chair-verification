module

public import SpectreFinite.ParentBoundaryFrameTable08
public import SpectreFinite.ParentBoundaryRow0105

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0105_states :
    FrameRows (indexedField parentRow0105) boundaryFrames08 := by decide

theorem boundaryFrameRow0105_structure :
    FramedRootStructure (indexedField parentRow0105) := by
  exact ⟨4,boundaryNeighbors03,boundaryFrames08,boundaryRow0105_shape,
    structure_of_table _ _ _ _ boundaryRow0105_sound
      boundaryTable03_covers boundaryTable03_structure,
    boundaryFrames08_geometry,boundaryFrameRow0105_states⟩

#print axioms boundaryFrameRow0105_structure
end SpectreFinite.HexSearch.ParentBoundary
