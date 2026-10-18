module

public import SpectreFinite.ParentBoundaryTable07
public import SpectreFinite.ParentOwnershipFinitePart078

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1263_shape :
    rootParent (indexedField parentRow1263) = childPatch 7 := by decide

theorem boundaryRow1263_sound :
    TableSound (indexedField parentRow1263) boundaryTable07 := by decide

theorem boundaryRow1263_structure : RootStructure (indexedField parentRow1263) := by
  exact ⟨7,boundaryNeighbors07,boundaryRow1263_shape,
    structure_of_table _ _ _ _ boundaryRow1263_sound
      boundaryTable07_covers boundaryTable07_structure⟩

#print axioms boundaryRow1263_structure
end SpectreFinite.HexSearch.ParentBoundary
