module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable10 : OwnerTable := [(((-1),2),((-2),3)),(((-1),1),((-2),3)),(((-1),0),((-3),1)),(((-1),(-1)),(1,(-3))),((0,(-2)),(1,(-3))),((1,(-2)),(1,(-3))),((2,(-3)),(3,(-3))),((3,(-3)),(3,(-3))),((3,(-2)),(3,0)),((3,(-1)),(3,0)),((2,0),(3,0)),((2,1),(1,3)),((1,2),(1,3)),((0,2),(1,3)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0)),((1,1),(0,0))]
def boundaryNeighbors10 : List Position := [((-2),3),((-3),1),(1,(-3)),(3,(-3)),(3,0),(1,3)]

theorem boundaryTable10_covers : ∀ x ∈ support 4,
    tableOwners boundaryTable10 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable10_structure :
    Structure (tableOwners boundaryTable10) 4 boundaryNeighbors10 := by decide

#print axioms boundaryTable10_structure
end SpectreFinite.HexSearch.ParentBoundary
