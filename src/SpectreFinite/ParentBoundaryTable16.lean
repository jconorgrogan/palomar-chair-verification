module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable16 : OwnerTable := [((0,2),((-2),3)),(((-1),2),((-2),3)),(((-1),1),((-2),3)),(((-1),0),((-2),1)),(((-1),(-1)),((-2),1)),((0,(-2)),(0,(-2))),((1,(-2)),(0,(-2))),((2,(-3)),(0,(-2))),((3,(-3)),(3,(-3))),((3,(-2)),(3,(-3))),((3,(-1)),(4,(-1))),((2,0),(4,(-1))),((2,1),(1,2)),((1,2),(1,2)),((1,1),(0,0)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0))]
def boundaryNeighbors16 : List Position := [((-2),3),((-2),1),(0,(-2)),(3,(-3)),(4,(-1)),(1,2)]

theorem boundaryTable16_covers : ∀ x ∈ support 1,
    tableOwners boundaryTable16 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable16_structure :
    Structure (tableOwners boundaryTable16) 1 boundaryNeighbors16 := by decide

#print axioms boundaryTable16_structure
end SpectreFinite.HexSearch.ParentBoundary
