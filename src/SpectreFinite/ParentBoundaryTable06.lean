module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable06 : OwnerTable := [((0,2),((-2),2)),(((-1),2),((-2),2)),(((-1),1),((-2),2)),(((-1),0),((-3),1)),(((-1),(-1)),(1,(-3))),((0,(-2)),(1,(-3))),((1,(-2)),(1,(-3))),((2,(-3)),(4,(-4))),((3,(-3)),(4,(-4))),((3,(-2)),(4,(-4))),((3,(-1)),(4,(-1))),((2,0),(4,(-1))),((2,1),(1,2)),((1,2),(1,2)),((1,1),(0,0)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0))]
def boundaryNeighbors06 : List Position := [((-2),2),((-3),1),(1,(-3)),(4,(-4)),(4,(-1)),(1,2)]

theorem boundaryTable06_covers : ∀ x ∈ support 7,
    tableOwners boundaryTable06 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable06_structure :
    Structure (tableOwners boundaryTable06) 7 boundaryNeighbors06 := by decide

#print axioms boundaryTable06_structure
end SpectreFinite.HexSearch.ParentBoundary
