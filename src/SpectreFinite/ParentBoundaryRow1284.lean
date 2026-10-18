module

public import SpectreFinite.ParentBoundaryTable13
public import SpectreFinite.ParentOwnershipFinitePart080

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1284_shape :
    rootParent (indexedField parentRow1284) = childPatch 7 := by decide

theorem boundaryRow1284_sound :
    TableSound (indexedField parentRow1284) boundaryTable13 := by decide

theorem boundaryRow1284_structure : RootStructure (indexedField parentRow1284) := by
  exact ⟨7,boundaryNeighbors13,boundaryRow1284_shape,
    structure_of_table _ _ _ _ boundaryRow1284_sound
      boundaryTable13_covers boundaryTable13_structure⟩

#print axioms boundaryRow1284_structure
end SpectreFinite.HexSearch.ParentBoundary
