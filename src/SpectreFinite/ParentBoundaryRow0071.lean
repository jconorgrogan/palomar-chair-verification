module

public import SpectreFinite.ParentBoundaryTable00
public import SpectreFinite.ParentOwnershipFinitePart004

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow0071_shape :
    rootParent (indexedField parentRow0071) = childPatch 6 := by decide

theorem boundaryRow0071_sound :
    TableSound (indexedField parentRow0071) boundaryTable00 := by decide

theorem boundaryRow0071_structure : RootStructure (indexedField parentRow0071) := by
  exact ⟨6,boundaryNeighbors00,boundaryRow0071_shape,
    structure_of_table _ _ _ _ boundaryRow0071_sound
      boundaryTable00_covers boundaryTable00_structure⟩

#print axioms boundaryRow0071_structure
end SpectreFinite.HexSearch.ParentBoundary
