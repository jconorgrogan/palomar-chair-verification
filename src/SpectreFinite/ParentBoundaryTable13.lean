module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable13 : OwnerTable := [((0,2),((-2),2)),(((-1),2),((-2),2)),(((-1),1),((-2),2)),(((-1),0),((-2),0)),(((-1),(-1)),(1,(-3))),((0,(-2)),(1,(-3))),((1,(-2)),(1,(-3))),((2,(-3)),(4,(-4))),((3,(-3)),(4,(-4))),((3,(-2)),(4,(-4))),((3,(-1)),(4,(-1))),((2,0),(4,(-1))),((2,1),(1,2)),((1,2),(1,2)),((1,1),(0,0)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0))]
def boundaryNeighbors13 : List Position := [((-2),2),((-2),0),(1,(-3)),(4,(-4)),(4,(-1)),(1,2)]

theorem boundaryTable13_covers : ∀ x ∈ support 7,
    tableOwners boundaryTable13 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable13_structure :
    Structure (tableOwners boundaryTable13) 7 boundaryNeighbors13 := by decide

#print axioms boundaryTable13_structure
end SpectreFinite.HexSearch.ParentBoundary
