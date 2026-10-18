module

public import SpectreFinite.ParentBoundaryTable01
public import SpectreFinite.ParentOwnershipFinitePart067

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1075_shape :
    rootParent (indexedField parentRow1075) = childPatch 0 := by decide

theorem boundaryRow1075_sound :
    TableSound (indexedField parentRow1075) boundaryTable01 := by decide

theorem boundaryRow1075_structure : RootStructure (indexedField parentRow1075) := by
  exact ⟨0,boundaryNeighbors01,boundaryRow1075_shape,
    structure_of_table _ _ _ _ boundaryRow1075_sound
      boundaryTable01_covers boundaryTable01_structure⟩

#print axioms boundaryRow1075_structure
end SpectreFinite.HexSearch.ParentBoundary
