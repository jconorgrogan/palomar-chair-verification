module

public import SpectreFinite.ParentBoundaryTable10
public import SpectreFinite.ParentOwnershipFinitePart079

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1274_shape :
    rootParent (indexedField parentRow1274) = childPatch 4 := by decide

theorem boundaryRow1274_sound :
    TableSound (indexedField parentRow1274) boundaryTable10 := by decide

theorem boundaryRow1274_structure : RootStructure (indexedField parentRow1274) := by
  exact ⟨4,boundaryNeighbors10,boundaryRow1274_shape,
    structure_of_table _ _ _ _ boundaryRow1274_sound
      boundaryTable10_covers boundaryTable10_structure⟩

#print axioms boundaryRow1274_structure
end SpectreFinite.HexSearch.ParentBoundary
