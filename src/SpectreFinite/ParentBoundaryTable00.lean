module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable00 : OwnerTable := [((0,2),((-1),2)),(((-1),2),((-1),2)),(((-1),1),((-2),0)),(((-1),0),((-2),0)),(((-1),(-1)),((-2),0)),((0,(-2)),(0,(-2))),((1,(-2)),(0,(-2))),((2,(-3)),(0,(-2))),((3,(-3)),(3,(-3))),((3,(-2)),(3,(-3))),((3,(-1)),(4,0)),((2,0),(4,0)),((2,1),(1,2)),((1,2),(1,2)),((1,1),(0,0)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0))]
def boundaryNeighbors00 : List Position := [((-1),2),((-2),0),(0,(-2)),(3,(-3)),(4,0),(1,2)]

theorem boundaryTable00_covers : ∀ x ∈ support 6,
    tableOwners boundaryTable00 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable00_structure :
    Structure (tableOwners boundaryTable00) 6 boundaryNeighbors00 := by decide

#print axioms boundaryTable00_structure
end SpectreFinite.HexSearch.ParentBoundary
