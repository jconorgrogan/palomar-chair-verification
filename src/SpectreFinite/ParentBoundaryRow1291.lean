module

public import SpectreFinite.ParentBoundaryTable15
public import SpectreFinite.ParentOwnershipFinitePart080

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1291_shape :
    rootParent (indexedField parentRow1291) = childPatch 1 := by decide

theorem boundaryRow1291_sound :
    TableSound (indexedField parentRow1291) boundaryTable15 := by decide

theorem boundaryRow1291_structure : RootStructure (indexedField parentRow1291) := by
  exact ⟨1,boundaryNeighbors15,boundaryRow1291_shape,
    structure_of_table _ _ _ _ boundaryRow1291_sound
      boundaryTable15_covers boundaryTable15_structure⟩

#print axioms boundaryRow1291_structure
end SpectreFinite.HexSearch.ParentBoundary
