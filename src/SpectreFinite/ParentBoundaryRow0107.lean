module

public import SpectreFinite.ParentBoundaryTable04
public import SpectreFinite.ParentOwnershipFinitePart006

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0107_shape :
    rootParent (indexedField parentRow0107) = childPatch 8 := by decide

theorem boundaryRow0107_sound :
    TableSound (indexedField parentRow0107) boundaryTable04 := by decide

theorem boundaryRow0107_structure : RootStructure (indexedField parentRow0107) := by
  exact ⟨8,boundaryNeighbors04,boundaryRow0107_shape,
    structure_of_table _ _ _ _ boundaryRow0107_sound
      boundaryTable04_covers boundaryTable04_structure⟩

#print axioms boundaryRow0107_structure
end SpectreFinite.HexSearch.ParentBoundary
