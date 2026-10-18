module

public import SpectreFinite.ParentBoundaryFrameTable06
public import SpectreFinite.ParentBoundaryRow0102

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0102_states :
    FrameRows (indexedField parentRow0102) boundaryFrames06 := by decide

theorem boundaryFrameRow0102_structure :
    FramedRootStructure (indexedField parentRow0102) := by
  exact ⟨5,boundaryNeighbors02,boundaryFrames06,boundaryRow0102_shape,
    structure_of_table _ _ _ _ boundaryRow0102_sound
      boundaryTable02_covers boundaryTable02_structure,
    boundaryFrames06_geometry,boundaryFrameRow0102_states⟩

#print axioms boundaryFrameRow0102_structure
end SpectreFinite.HexSearch.ParentBoundary
