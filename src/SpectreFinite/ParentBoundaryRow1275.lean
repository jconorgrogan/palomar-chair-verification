module

public import SpectreFinite.ParentBoundaryTable11
public import SpectreFinite.ParentOwnershipFinitePart079

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1275_shape :
    rootParent (indexedField parentRow1275) = childPatch 8 := by decide

theorem boundaryRow1275_sound :
    TableSound (indexedField parentRow1275) boundaryTable11 := by decide

theorem boundaryRow1275_structure : RootStructure (indexedField parentRow1275) := by
  exact ⟨8,boundaryNeighbors11,boundaryRow1275_shape,
    structure_of_table _ _ _ _ boundaryRow1275_sound
      boundaryTable11_covers boundaryTable11_structure⟩

#print axioms boundaryRow1275_structure
end SpectreFinite.HexSearch.ParentBoundary
