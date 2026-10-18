module

public import SpectreFinite.ParentBoundaryTable16
public import SpectreFinite.ParentOwnershipFinitePart080

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1287_shape :
    rootParent (indexedField parentRow1287) = childPatch 1 := by decide

theorem boundaryRow1287_sound :
    TableSound (indexedField parentRow1287) boundaryTable16 := by decide

theorem boundaryRow1287_structure : RootStructure (indexedField parentRow1287) := by
  exact ⟨1,boundaryNeighbors16,boundaryRow1287_shape,
    structure_of_table _ _ _ _ boundaryRow1287_sound
      boundaryTable16_covers boundaryTable16_structure⟩

#print axioms boundaryRow1287_structure
end SpectreFinite.HexSearch.ParentBoundary
