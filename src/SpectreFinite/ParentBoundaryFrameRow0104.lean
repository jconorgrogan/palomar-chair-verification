module

public import SpectreFinite.ParentBoundaryFrameTable08
public import SpectreFinite.ParentBoundaryRow0104

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0104_states :
    FrameRows (indexedField parentRow0104) boundaryFrames08 := by decide

theorem boundaryFrameRow0104_structure :
    FramedRootStructure (indexedField parentRow0104) := by
  exact ⟨4,boundaryNeighbors03,boundaryFrames08,boundaryRow0104_shape,
    structure_of_table _ _ _ _ boundaryRow0104_sound
      boundaryTable03_covers boundaryTable03_structure,
    boundaryFrames08_geometry,boundaryFrameRow0104_states⟩

#print axioms boundaryFrameRow0104_structure
end SpectreFinite.HexSearch.ParentBoundary
