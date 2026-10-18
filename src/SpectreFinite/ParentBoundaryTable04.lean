module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable04 : OwnerTable := [(((-1),2),((-3),3)),(((-1),1),((-3),3)),(((-1),0),((-3),1)),(((-1),(-1)),(1,(-3))),((0,(-2)),(1,(-3))),((1,(-2)),(1,(-3))),((2,(-3)),(4,(-4))),((3,(-3)),(4,(-4))),((3,(-2)),(4,(-4))),((3,(-1)),(4,(-1))),((2,0),(4,(-1))),((2,1),(1,3)),((1,2),(1,3)),((0,2),(1,3)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0)),((1,1),(0,0))]
def boundaryNeighbors04 : List Position := [((-3),3),((-3),1),(1,(-3)),(4,(-4)),(4,(-1)),(1,3)]

theorem boundaryTable04_covers : ∀ x ∈ support 8,
    tableOwners boundaryTable04 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable04_structure :
    Structure (tableOwners boundaryTable04) 8 boundaryNeighbors04 := by decide

#print axioms boundaryTable04_structure
end SpectreFinite.HexSearch.ParentBoundary
