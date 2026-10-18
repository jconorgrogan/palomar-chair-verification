module

public import SpectreFinite.ParentBoundaryTable03
public import SpectreFinite.ParentOwnershipFinitePart006

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0111_shape :
    rootParent (indexedField parentRow0111) = childPatch 4 := by decide

theorem boundaryRow0111_sound :
    TableSound (indexedField parentRow0111) boundaryTable03 := by decide

theorem boundaryRow0111_structure : RootStructure (indexedField parentRow0111) := by
  exact ⟨4,boundaryNeighbors03,boundaryRow0111_shape,
    structure_of_table _ _ _ _ boundaryRow0111_sound
      boundaryTable03_covers boundaryTable03_structure⟩

#print axioms boundaryRow0111_structure
end SpectreFinite.HexSearch.ParentBoundary
