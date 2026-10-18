module

public import SpectreFinite.ParentBoundaryTable08
public import SpectreFinite.ParentOwnershipFinitePart079

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1266_shape :
    rootParent (indexedField parentRow1266) = childPatch 2 := by decide

theorem boundaryRow1266_sound :
    TableSound (indexedField parentRow1266) boundaryTable08 := by decide

theorem boundaryRow1266_structure : RootStructure (indexedField parentRow1266) := by
  exact ⟨2,boundaryNeighbors08,boundaryRow1266_shape,
    structure_of_table _ _ _ _ boundaryRow1266_sound
      boundaryTable08_covers boundaryTable08_structure⟩

#print axioms boundaryRow1266_structure
end SpectreFinite.HexSearch.ParentBoundary
