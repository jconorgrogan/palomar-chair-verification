module

public import SpectreFinite.ParentBoundaryTable02
public import SpectreFinite.ParentOwnershipFinitePart032

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0514_shape :
    rootParent (indexedField parentRow0514) = childPatch 5 := by decide

theorem boundaryRow0514_sound :
    TableSound (indexedField parentRow0514) boundaryTable02 := by decide

theorem boundaryRow0514_structure : RootStructure (indexedField parentRow0514) := by
  exact ⟨5,boundaryNeighbors02,boundaryRow0514_shape,
    structure_of_table _ _ _ _ boundaryRow0514_sound
      boundaryTable02_covers boundaryTable02_structure⟩

#print axioms boundaryRow0514_structure
end SpectreFinite.HexSearch.ParentBoundary
