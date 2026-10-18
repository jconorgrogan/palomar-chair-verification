module

public import SpectreFinite.ParentBoundaryTable10
public import SpectreFinite.ParentOwnershipFinitePart079

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1279_shape :
    rootParent (indexedField parentRow1279) = childPatch 4 := by decide

theorem boundaryRow1279_sound :
    TableSound (indexedField parentRow1279) boundaryTable10 := by decide

theorem boundaryRow1279_structure : RootStructure (indexedField parentRow1279) := by
  exact ⟨4,boundaryNeighbors10,boundaryRow1279_shape,
    structure_of_table _ _ _ _ boundaryRow1279_sound
      boundaryTable10_covers boundaryTable10_structure⟩

#print axioms boundaryRow1279_structure
end SpectreFinite.HexSearch.ParentBoundary
