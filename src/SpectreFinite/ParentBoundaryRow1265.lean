module

public import SpectreFinite.ParentBoundaryTable06
public import SpectreFinite.ParentOwnershipFinitePart079

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1265_shape :
    rootParent (indexedField parentRow1265) = childPatch 7 := by decide

theorem boundaryRow1265_sound :
    TableSound (indexedField parentRow1265) boundaryTable06 := by decide

theorem boundaryRow1265_structure : RootStructure (indexedField parentRow1265) := by
  exact ⟨7,boundaryNeighbors06,boundaryRow1265_shape,
    structure_of_table _ _ _ _ boundaryRow1265_sound
      boundaryTable06_covers boundaryTable06_structure⟩

#print axioms boundaryRow1265_structure
end SpectreFinite.HexSearch.ParentBoundary
