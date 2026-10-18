module

public import SpectreFinite.ParentBoundaryTable04
public import SpectreFinite.ParentOwnershipFinitePart006

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0106_shape :
    rootParent (indexedField parentRow0106) = childPatch 8 := by decide

theorem boundaryRow0106_sound :
    TableSound (indexedField parentRow0106) boundaryTable04 := by decide

theorem boundaryRow0106_structure : RootStructure (indexedField parentRow0106) := by
  exact ⟨8,boundaryNeighbors04,boundaryRow0106_shape,
    structure_of_table _ _ _ _ boundaryRow0106_sound
      boundaryTable04_covers boundaryTable04_structure⟩

#print axioms boundaryRow0106_structure
end SpectreFinite.HexSearch.ParentBoundary
