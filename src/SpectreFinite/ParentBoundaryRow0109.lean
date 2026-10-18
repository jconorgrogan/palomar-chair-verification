module

public import SpectreFinite.ParentBoundaryTable02
public import SpectreFinite.ParentOwnershipFinitePart006

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0109_shape :
    rootParent (indexedField parentRow0109) = childPatch 5 := by decide

theorem boundaryRow0109_sound :
    TableSound (indexedField parentRow0109) boundaryTable02 := by decide

theorem boundaryRow0109_structure : RootStructure (indexedField parentRow0109) := by
  exact ⟨5,boundaryNeighbors02,boundaryRow0109_shape,
    structure_of_table _ _ _ _ boundaryRow0109_sound
      boundaryTable02_covers boundaryTable02_structure⟩

#print axioms boundaryRow0109_structure
end SpectreFinite.HexSearch.ParentBoundary
