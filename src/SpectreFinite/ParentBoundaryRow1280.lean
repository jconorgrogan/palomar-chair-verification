module

public import SpectreFinite.ParentBoundaryTable12
public import SpectreFinite.ParentOwnershipFinitePart080

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1280_shape :
    rootParent (indexedField parentRow1280) = childPatch 3 := by decide

theorem boundaryRow1280_sound :
    TableSound (indexedField parentRow1280) boundaryTable12 := by decide

theorem boundaryRow1280_structure : RootStructure (indexedField parentRow1280) := by
  exact ⟨3,boundaryNeighbors12,boundaryRow1280_shape,
    structure_of_table _ _ _ _ boundaryRow1280_sound
      boundaryTable12_covers boundaryTable12_structure⟩

#print axioms boundaryRow1280_structure
end SpectreFinite.HexSearch.ParentBoundary
