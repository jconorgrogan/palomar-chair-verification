module

public import SpectreFinite.ParentBoundaryFrameTable07
public import SpectreFinite.ParentBoundaryRow0103

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0103_states :
    FrameRows (indexedField parentRow0103) boundaryFrames07 := by decide

theorem boundaryFrameRow0103_structure :
    FramedRootStructure (indexedField parentRow0103) := by
  exact ⟨5,boundaryNeighbors02,boundaryFrames07,boundaryRow0103_shape,
    structure_of_table _ _ _ _ boundaryRow0103_sound
      boundaryTable02_covers boundaryTable02_structure,
    boundaryFrames07_geometry,boundaryFrameRow0103_states⟩

#print axioms boundaryFrameRow0103_structure
end SpectreFinite.HexSearch.ParentBoundary
