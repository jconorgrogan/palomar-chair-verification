module

public import SpectreFinite.ParentBoundaryTable03
public import SpectreFinite.ParentOwnershipFinitePart006

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0105_shape :
    rootParent (indexedField parentRow0105) = childPatch 4 := by decide

theorem boundaryRow0105_sound :
    TableSound (indexedField parentRow0105) boundaryTable03 := by decide

theorem boundaryRow0105_structure : RootStructure (indexedField parentRow0105) := by
  exact ⟨4,boundaryNeighbors03,boundaryRow0105_shape,
    structure_of_table _ _ _ _ boundaryRow0105_sound
      boundaryTable03_covers boundaryTable03_structure⟩

#print axioms boundaryRow0105_structure
end SpectreFinite.HexSearch.ParentBoundary
