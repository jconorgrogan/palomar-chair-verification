module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable11 : OwnerTable := [(((-1),2),((-2),3)),(((-1),1),((-2),3)),(((-1),0),((-3),1)),(((-1),(-1)),(1,(-3))),((0,(-2)),(1,(-3))),((1,(-2)),(1,(-3))),((2,(-3)),(4,(-4))),((3,(-3)),(4,(-4))),((3,(-2)),(4,(-4))),((3,(-1)),(4,(-1))),((2,0),(4,(-1))),((2,1),(1,3)),((1,2),(1,3)),((0,2),(1,3)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-2)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0)),((1,1),(0,0))]
def boundaryNeighbors11 : List Position := [((-2),3),((-3),1),(1,(-3)),(4,(-4)),(4,(-1)),(1,3)]

theorem boundaryTable11_covers : ∀ x ∈ support 8,
    tableOwners boundaryTable11 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable11_structure :
    Structure (tableOwners boundaryTable11) 8 boundaryNeighbors11 := by decide

#print axioms boundaryTable11_structure
end SpectreFinite.HexSearch.ParentBoundary
