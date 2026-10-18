module

public import SpectreFinite.ParentBoundaryTable14
public import SpectreFinite.ParentOwnershipFinitePart080

@[expose] public section


/-! Boundary and native-vertex certificate for one literal radius-five row. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem boundaryRow1282_shape :
    rootParent (indexedField parentRow1282) = childPatch 7 := by decide

theorem boundaryRow1282_sound :
    TableSound (indexedField parentRow1282) boundaryTable14 := by decide

theorem boundaryRow1282_structure : RootStructure (indexedField parentRow1282) := by
  exact ⟨7,boundaryNeighbors14,boundaryRow1282_shape,
    structure_of_table _ _ _ _ boundaryRow1282_sound
      boundaryTable14_covers boundaryTable14_structure⟩

#print axioms boundaryRow1282_structure
end SpectreFinite.HexSearch.ParentBoundary
