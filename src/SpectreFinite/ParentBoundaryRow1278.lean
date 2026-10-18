module

public import SpectreFinite.ParentBoundaryTable11
public import SpectreFinite.ParentOwnershipFinitePart079

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1278_shape :
    rootParent (indexedField parentRow1278) = childPatch 8 := by decide

theorem boundaryRow1278_sound :
    TableSound (indexedField parentRow1278) boundaryTable11 := by decide

theorem boundaryRow1278_structure : RootStructure (indexedField parentRow1278) := by
  exact ⟨8,boundaryNeighbors11,boundaryRow1278_shape,
    structure_of_table _ _ _ _ boundaryRow1278_sound
      boundaryTable11_covers boundaryTable11_structure⟩

#print axioms boundaryRow1278_structure
end SpectreFinite.HexSearch.ParentBoundary
