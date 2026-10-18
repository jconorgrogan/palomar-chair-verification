module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable15 : OwnerTable := [((0,2),((-2),3)),(((-1),2),((-2),3)),(((-1),1),((-2),3)),(((-1),0),((-2),1)),(((-1),(-1)),((-2),1)),((0,(-2)),(0,(-2))),((1,(-2)),(0,(-2))),((2,(-3)),(0,(-2))),((3,(-3)),(3,(-3))),((3,(-2)),(3,(-3))),((3,(-1)),(4,0)),((2,0),(4,0)),((2,1),(1,2)),((1,2),(1,2)),((1,1),(0,0)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0))]
def boundaryNeighbors15 : List Position := [((-2),3),((-2),1),(0,(-2)),(3,(-3)),(4,0),(1,2)]

theorem boundaryTable15_covers : ∀ x ∈ support 1,
    tableOwners boundaryTable15 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable15_structure :
    Structure (tableOwners boundaryTable15) 1 boundaryNeighbors15 := by decide

#print axioms boundaryTable15_structure
end SpectreFinite.HexSearch.ParentBoundary
