module

public import SpectreFinite.ParentBoundaryTable03
public import SpectreFinite.ParentOwnershipFinitePart006

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0110_shape :
    rootParent (indexedField parentRow0110) = childPatch 4 := by decide

theorem boundaryRow0110_sound :
    TableSound (indexedField parentRow0110) boundaryTable03 := by decide

theorem boundaryRow0110_structure : RootStructure (indexedField parentRow0110) := by
  exact ⟨4,boundaryNeighbors03,boundaryRow0110_shape,
    structure_of_table _ _ _ _ boundaryRow0110_sound
      boundaryTable03_covers boundaryTable03_structure⟩

#print axioms boundaryRow0110_structure
end SpectreFinite.HexSearch.ParentBoundary
