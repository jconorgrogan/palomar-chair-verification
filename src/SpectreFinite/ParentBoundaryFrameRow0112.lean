module

public import SpectreFinite.ParentBoundaryFrameTable14
public import SpectreFinite.ParentBoundaryRow0112

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow0112_states :
    FrameRows (indexedField parentRow0112) boundaryFrames14 := by decide

theorem boundaryFrameRow0112_structure :
    FramedRootStructure (indexedField parentRow0112) := by
  exact ⟨8,boundaryNeighbors04,boundaryFrames14,boundaryRow0112_shape,
    structure_of_table _ _ _ _ boundaryRow0112_sound
      boundaryTable04_covers boundaryTable04_structure,
    boundaryFrames14_geometry,boundaryFrameRow0112_states⟩

#print axioms boundaryFrameRow0112_structure
end SpectreFinite.HexSearch.ParentBoundary
