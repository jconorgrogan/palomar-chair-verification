module

public import SpectreFinite.ParentBoundaryTable11
public import SpectreFinite.ParentOwnershipFinitePart079

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1276_shape :
    rootParent (indexedField parentRow1276) = childPatch 8 := by decide

theorem boundaryRow1276_sound :
    TableSound (indexedField parentRow1276) boundaryTable11 := by decide

theorem boundaryRow1276_structure : RootStructure (indexedField parentRow1276) := by
  exact ⟨8,boundaryNeighbors11,boundaryRow1276_shape,
    structure_of_table _ _ _ _ boundaryRow1276_sound
      boundaryTable11_covers boundaryTable11_structure⟩

#print axioms boundaryRow1276_structure
end SpectreFinite.HexSearch.ParentBoundary
