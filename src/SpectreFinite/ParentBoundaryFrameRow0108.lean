module

public import SpectreFinite.ParentBoundaryFrameTable11
public import SpectreFinite.ParentBoundaryRow0108

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0108_states :
    FrameRows (indexedField parentRow0108) boundaryFrames11 := by decide

theorem boundaryFrameRow0108_structure :
    FramedRootStructure (indexedField parentRow0108) := by
  exact ⟨0,boundaryNeighbors05,boundaryFrames11,boundaryRow0108_shape,
    structure_of_table _ _ _ _ boundaryRow0108_sound
      boundaryTable05_covers boundaryTable05_structure,
    boundaryFrames11_geometry,boundaryFrameRow0108_states⟩

#print axioms boundaryFrameRow0108_structure
end SpectreFinite.HexSearch.ParentBoundary
