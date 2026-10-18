module

public import SpectreFinite.ParentBoundaryTable02
public import SpectreFinite.ParentOwnershipFinitePart006

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0103_shape :
    rootParent (indexedField parentRow0103) = childPatch 5 := by decide

theorem boundaryRow0103_sound :
    TableSound (indexedField parentRow0103) boundaryTable02 := by decide

theorem boundaryRow0103_structure : RootStructure (indexedField parentRow0103) := by
  exact ⟨5,boundaryNeighbors02,boundaryRow0103_shape,
    structure_of_table _ _ _ _ boundaryRow0103_sound
      boundaryTable02_covers boundaryTable02_structure⟩

#print axioms boundaryRow0103_structure
end SpectreFinite.HexSearch.ParentBoundary
