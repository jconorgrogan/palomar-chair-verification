module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable12 : OwnerTable := [((0,2),((-2),2)),(((-1),2),((-2),2)),(((-1),1),((-2),2)),(((-1),0),((-2),0)),(((-1),(-1)),(0,(-3))),((0,(-2)),(0,(-3))),((1,(-2)),(0,(-3))),((2,(-3)),(0,(-3))),((3,(-3)),(3,(-3))),((3,(-2)),(3,(-3))),((3,(-1)),(4,(-1))),((2,0),(4,(-1))),((2,1),(1,2)),((1,2),(1,2)),((1,1),(0,0)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0))]
def boundaryNeighbors12 : List Position := [((-2),2),((-2),0),(0,(-3)),(3,(-3)),(4,(-1)),(1,2)]

theorem boundaryTable12_covers : ∀ x ∈ support 3,
    tableOwners boundaryTable12 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable12_structure :
    Structure (tableOwners boundaryTable12) 3 boundaryNeighbors12 := by decide

#print axioms boundaryTable12_structure
end SpectreFinite.HexSearch.ParentBoundary
