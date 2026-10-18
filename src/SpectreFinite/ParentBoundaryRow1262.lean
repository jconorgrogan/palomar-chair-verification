module

public import SpectreFinite.ParentBoundaryTable06
public import SpectreFinite.ParentOwnershipFinitePart078

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1262_shape :
    rootParent (indexedField parentRow1262) = childPatch 7 := by decide

theorem boundaryRow1262_sound :
    TableSound (indexedField parentRow1262) boundaryTable06 := by decide

theorem boundaryRow1262_structure : RootStructure (indexedField parentRow1262) := by
  exact ⟨7,boundaryNeighbors06,boundaryRow1262_shape,
    structure_of_table _ _ _ _ boundaryRow1262_sound
      boundaryTable06_covers boundaryTable06_structure⟩

#print axioms boundaryRow1262_structure
end SpectreFinite.HexSearch.ParentBoundary
