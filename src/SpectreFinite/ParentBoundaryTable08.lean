module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable08 : OwnerTable := [((0,2),((-2),2)),(((-1),2),((-2),2)),(((-1),1),((-2),2)),(((-1),0),((-3),1)),(((-1),(-1)),(1,(-3))),((0,(-2)),(1,(-3))),((1,(-2)),(1,(-3))),((2,(-3)),(3,(-3))),((3,(-3)),(3,(-3))),((3,(-2)),(3,0)),((3,(-1)),(3,0)),((2,0),(3,0)),((2,1),(1,2)),((1,2),(1,2)),((1,1),(0,0)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0))]
def boundaryNeighbors08 : List Position := [((-2),2),((-3),1),(1,(-3)),(3,(-3)),(3,0),(1,2)]

theorem boundaryTable08_covers : ∀ x ∈ support 2,
    tableOwners boundaryTable08 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable08_structure :
    Structure (tableOwners boundaryTable08) 2 boundaryNeighbors08 := by decide

#print axioms boundaryTable08_structure
end SpectreFinite.HexSearch.ParentBoundary
