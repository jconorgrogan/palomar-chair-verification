module

public import SpectreFinite.ParentBoundaryFrameTable34
public import SpectreFinite.ParentBoundaryRow1284

@[expose] public section


/-! Kernel checks of the actual neighboring Gamma turns and unique projected
parent kinds in one literal radius-five row. Global parent-shape binding is
provided only by the explicit theorem in ParentBoundaryFrameTransfer. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryFrameRow1284_states :
    FrameRows (indexedField parentRow1284) boundaryFrames34 := by decide

theorem boundaryFrameRow1284_structure :
    FramedRootStructure (indexedField parentRow1284) := by
  exact ⟨7,boundaryNeighbors13,boundaryFrames34,boundaryRow1284_shape,
    structure_of_table _ _ _ _ boundaryRow1284_sound
      boundaryTable13_covers boundaryTable13_structure,
    boundaryFrames34_geometry,boundaryFrameRow1284_states⟩

#print axioms boundaryFrameRow1284_structure
end SpectreFinite.HexSearch.ParentBoundary
