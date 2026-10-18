module

public import SpectreFinite.ParentBoundaryTable00
public import SpectreFinite.ParentOwnershipFinitePart004

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0065_shape :
    rootParent (indexedField parentRow0065) = childPatch 6 := by decide

theorem boundaryRow0065_sound :
    TableSound (indexedField parentRow0065) boundaryTable00 := by decide

theorem boundaryRow0065_structure : RootStructure (indexedField parentRow0065) := by
  exact ⟨6,boundaryNeighbors00,boundaryRow0065_shape,
    structure_of_table _ _ _ _ boundaryRow0065_sound
      boundaryTable00_covers boundaryTable00_structure⟩

#print axioms boundaryRow0065_structure
end SpectreFinite.HexSearch.ParentBoundary
