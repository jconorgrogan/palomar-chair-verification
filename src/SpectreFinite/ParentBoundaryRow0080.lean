module

public import SpectreFinite.ParentBoundaryTable01
public import SpectreFinite.ParentOwnershipFinitePart005

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0080_shape :
    rootParent (indexedField parentRow0080) = childPatch 0 := by decide

theorem boundaryRow0080_sound :
    TableSound (indexedField parentRow0080) boundaryTable01 := by decide

theorem boundaryRow0080_structure : RootStructure (indexedField parentRow0080) := by
  exact ⟨0,boundaryNeighbors01,boundaryRow0080_shape,
    structure_of_table _ _ _ _ boundaryRow0080_sound
      boundaryTable01_covers boundaryTable01_structure⟩

#print axioms boundaryRow0080_structure
end SpectreFinite.HexSearch.ParentBoundary
