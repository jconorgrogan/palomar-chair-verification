module

public import SpectreFinite.ParentBoundaryTable01
public import SpectreFinite.ParentOwnershipFinitePart019

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0308_shape :
    rootParent (indexedField parentRow0308) = childPatch 0 := by decide

theorem boundaryRow0308_sound :
    TableSound (indexedField parentRow0308) boundaryTable01 := by decide

theorem boundaryRow0308_structure : RootStructure (indexedField parentRow0308) := by
  exact ⟨0,boundaryNeighbors01,boundaryRow0308_shape,
    structure_of_table _ _ _ _ boundaryRow0308_sound
      boundaryTable01_covers boundaryTable01_structure⟩

#print axioms boundaryRow0308_structure
end SpectreFinite.HexSearch.ParentBoundary
