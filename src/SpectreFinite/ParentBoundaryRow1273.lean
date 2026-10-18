module

public import SpectreFinite.ParentBoundaryTable09
public import SpectreFinite.ParentOwnershipFinitePart079

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1273_shape :
    rootParent (indexedField parentRow1273) = childPatch 5 := by decide

theorem boundaryRow1273_sound :
    TableSound (indexedField parentRow1273) boundaryTable09 := by decide

theorem boundaryRow1273_structure : RootStructure (indexedField parentRow1273) := by
  exact ⟨5,boundaryNeighbors09,boundaryRow1273_shape,
    structure_of_table _ _ _ _ boundaryRow1273_sound
      boundaryTable09_covers boundaryTable09_structure⟩

#print axioms boundaryRow1273_structure
end SpectreFinite.HexSearch.ParentBoundary
