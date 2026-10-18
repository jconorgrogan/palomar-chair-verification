module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable05 : OwnerTable := [(((-1),2),((-3),3)),(((-1),1),((-3),3)),(((-1),0),((-3),1)),(((-1),(-1)),(0,(-2))),((0,(-2)),(0,(-2))),((1,(-2)),(2,(-2))),((2,(-2)),(2,(-2))),((3,(-2)),(2,(-2))),((3,(-1)),(3,(-1))),((2,0),(3,(-1))),((2,1),(3,(-1))),((1,2),(1,2)),((0,2),(1,2)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0)),((1,1),(0,0))]
def boundaryNeighbors05 : List Position := [((-3),3),((-3),1),(0,(-2)),(2,(-2)),(3,(-1)),(1,2)]

theorem boundaryTable05_covers : ∀ x ∈ support 0,
    tableOwners boundaryTable05 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable05_structure :
    Structure (tableOwners boundaryTable05) 0 boundaryNeighbors05 := by decide

#print axioms boundaryTable05_structure
end SpectreFinite.HexSearch.ParentBoundary
