module

public import SpectreFinite.ParentBoundaryTable13
public import SpectreFinite.ParentOwnershipFinitePart080

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1281_shape :
    rootParent (indexedField parentRow1281) = childPatch 7 := by decide

theorem boundaryRow1281_sound :
    TableSound (indexedField parentRow1281) boundaryTable13 := by decide

theorem boundaryRow1281_structure : RootStructure (indexedField parentRow1281) := by
  exact ⟨7,boundaryNeighbors13,boundaryRow1281_shape,
    structure_of_table _ _ _ _ boundaryRow1281_sound
      boundaryTable13_covers boundaryTable13_structure⟩

#print axioms boundaryRow1281_structure
end SpectreFinite.HexSearch.ParentBoundary
