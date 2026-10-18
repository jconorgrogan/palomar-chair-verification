module

public import SpectreFinite.ParentBoundaryTable00
public import SpectreFinite.ParentOwnershipFinitePart004

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0064_shape :
    rootParent (indexedField parentRow0064) = childPatch 6 := by decide

theorem boundaryRow0064_sound :
    TableSound (indexedField parentRow0064) boundaryTable00 := by decide

theorem boundaryRow0064_structure : RootStructure (indexedField parentRow0064) := by
  exact ⟨6,boundaryNeighbors00,boundaryRow0064_shape,
    structure_of_table _ _ _ _ boundaryRow0064_sound
      boundaryTable00_covers boundaryTable00_structure⟩

#print axioms boundaryRow0064_structure
end SpectreFinite.HexSearch.ParentBoundary
