module

public import SpectreFinite.ParentBoundaryTable15
public import SpectreFinite.ParentOwnershipFinitePart080

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1289_shape :
    rootParent (indexedField parentRow1289) = childPatch 1 := by decide

theorem boundaryRow1289_sound :
    TableSound (indexedField parentRow1289) boundaryTable15 := by decide

theorem boundaryRow1289_structure : RootStructure (indexedField parentRow1289) := by
  exact ⟨1,boundaryNeighbors15,boundaryRow1289_shape,
    structure_of_table _ _ _ _ boundaryRow1289_sound
      boundaryTable15_covers boundaryTable15_structure⟩

#print axioms boundaryRow1289_structure
end SpectreFinite.HexSearch.ParentBoundary
