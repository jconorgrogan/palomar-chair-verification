module

public import SpectreFinite.ParentBoundaryTable05
public import SpectreFinite.ParentOwnershipFinitePart006

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0108_shape :
    rootParent (indexedField parentRow0108) = childPatch 0 := by decide

theorem boundaryRow0108_sound :
    TableSound (indexedField parentRow0108) boundaryTable05 := by decide

theorem boundaryRow0108_structure : RootStructure (indexedField parentRow0108) := by
  exact ⟨0,boundaryNeighbors05,boundaryRow0108_shape,
    structure_of_table _ _ _ _ boundaryRow0108_sound
      boundaryTable05_covers boundaryTable05_structure⟩

#print axioms boundaryRow0108_structure
end SpectreFinite.HexSearch.ParentBoundary
