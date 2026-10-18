module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable03 : OwnerTable := [(((-1),2),((-3),3)),(((-1),1),((-3),3)),(((-1),0),((-3),1)),(((-1),(-1)),(1,(-3))),((0,(-2)),(1,(-3))),((1,(-2)),(1,(-3))),((2,(-3)),(3,(-3))),((3,(-3)),(3,(-3))),((3,(-2)),(3,0)),((3,(-1)),(3,0)),((2,0),(3,0)),((2,1),(1,3)),((1,2),(1,3)),((0,2),(1,3)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0)),((1,1),(0,0))]
def boundaryNeighbors03 : List Position := [((-3),3),((-3),1),(1,(-3)),(3,(-3)),(3,0),(1,3)]

theorem boundaryTable03_covers : ∀ x ∈ support 4,
    tableOwners boundaryTable03 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable03_structure :
    Structure (tableOwners boundaryTable03) 4 boundaryNeighbors03 := by decide

#print axioms boundaryTable03_structure
end SpectreFinite.HexSearch.ParentBoundary
