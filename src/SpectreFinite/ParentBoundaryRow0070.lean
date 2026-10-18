module

public import SpectreFinite.ParentBoundaryTable00
public import SpectreFinite.ParentOwnershipFinitePart004

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0070_shape :
    rootParent (indexedField parentRow0070) = childPatch 6 := by decide

theorem boundaryRow0070_sound :
    TableSound (indexedField parentRow0070) boundaryTable00 := by decide

theorem boundaryRow0070_structure : RootStructure (indexedField parentRow0070) := by
  exact ⟨6,boundaryNeighbors00,boundaryRow0070_shape,
    structure_of_table _ _ _ _ boundaryRow0070_sound
      boundaryTable00_covers boundaryTable00_structure⟩

#print axioms boundaryRow0070_structure
end SpectreFinite.HexSearch.ParentBoundary
