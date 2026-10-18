module

public import SpectreFinite.ParentBoundaryTable07
public import SpectreFinite.ParentOwnershipFinitePart079

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1264_shape :
    rootParent (indexedField parentRow1264) = childPatch 7 := by decide

theorem boundaryRow1264_sound :
    TableSound (indexedField parentRow1264) boundaryTable07 := by decide

theorem boundaryRow1264_structure : RootStructure (indexedField parentRow1264) := by
  exact ⟨7,boundaryNeighbors07,boundaryRow1264_shape,
    structure_of_table _ _ _ _ boundaryRow1264_sound
      boundaryTable07_covers boundaryTable07_structure⟩

#print axioms boundaryRow1264_structure
end SpectreFinite.HexSearch.ParentBoundary
