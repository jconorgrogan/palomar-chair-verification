module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable09 : OwnerTable := [(((-1),2),((-2),3)),(((-1),1),((-2),3)),(((-1),0),((-3),1)),(((-1),(-1)),(0,(-3))),((0,(-2)),(0,(-3))),((1,(-2)),(0,(-3))),((2,(-3)),(0,(-3))),((3,(-3)),(3,(-3))),((3,(-2)),(3,(-3))),((3,(-1)),(4,(-1))),((2,0),(4,(-1))),((2,1),(1,3)),((1,2),(1,3)),((0,2),(1,3)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0)),((1,1),(0,0))]
def boundaryNeighbors09 : List Position := [((-2),3),((-3),1),(0,(-3)),(3,(-3)),(4,(-1)),(1,3)]

theorem boundaryTable09_covers : ∀ x ∈ support 5,
    tableOwners boundaryTable09 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable09_structure :
    Structure (tableOwners boundaryTable09) 5 boundaryNeighbors09 := by decide

#print axioms boundaryTable09_structure
end SpectreFinite.HexSearch.ParentBoundary
