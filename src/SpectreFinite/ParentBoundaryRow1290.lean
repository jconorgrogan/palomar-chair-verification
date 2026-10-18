module

public import SpectreFinite.ParentBoundaryTable15
public import SpectreFinite.ParentOwnershipFinitePart080

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1290_shape :
    rootParent (indexedField parentRow1290) = childPatch 1 := by decide

theorem boundaryRow1290_sound :
    TableSound (indexedField parentRow1290) boundaryTable15 := by decide

theorem boundaryRow1290_structure : RootStructure (indexedField parentRow1290) := by
  exact ⟨1,boundaryNeighbors15,boundaryRow1290_shape,
    structure_of_table _ _ _ _ boundaryRow1290_sound
      boundaryTable15_covers boundaryTable15_structure⟩

#print axioms boundaryRow1290_structure
end SpectreFinite.HexSearch.ParentBoundary
