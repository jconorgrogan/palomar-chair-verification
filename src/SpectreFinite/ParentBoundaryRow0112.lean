module

public import SpectreFinite.ParentBoundaryTable04
public import SpectreFinite.ParentOwnershipFinitePart007

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0112_shape :
    rootParent (indexedField parentRow0112) = childPatch 8 := by decide

theorem boundaryRow0112_sound :
    TableSound (indexedField parentRow0112) boundaryTable04 := by decide

theorem boundaryRow0112_structure : RootStructure (indexedField parentRow0112) := by
  exact ⟨8,boundaryNeighbors04,boundaryRow0112_shape,
    structure_of_table _ _ _ _ boundaryRow0112_sound
      boundaryTable04_covers boundaryTable04_structure⟩

#print axioms boundaryRow0112_structure
end SpectreFinite.HexSearch.ParentBoundary
