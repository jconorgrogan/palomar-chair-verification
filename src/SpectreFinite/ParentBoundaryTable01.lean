module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Untrusted witness values, validated below by ordinary kernel reduction. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def boundaryTable01 : OwnerTable := [(((-1),2),((-3),3)),(((-1),1),((-3),3)),(((-1),0),((-3),0)),(((-1),(-1)),(0,(-2))),((0,(-2)),(0,(-2))),((1,(-2)),(2,(-2))),((2,(-2)),(2,(-2))),((3,(-2)),(2,(-2))),((3,(-1)),(3,(-1))),((2,0),(3,(-1))),((2,1),(3,(-1))),((1,2),(1,2)),((0,2),(1,2)),((0,1),(0,0)),((0,0),(0,0)),((0,(-1)),(0,0)),((1,(-1)),(0,0)),((2,(-1)),(0,0)),((1,0),(0,0)),((1,1),(0,0))]
def boundaryNeighbors01 : List Position := [((-3),3),((-3),0),(0,(-2)),(2,(-2)),(3,(-1)),(1,2)]

theorem boundaryTable01_covers : ∀ x ∈ support 0,
    tableOwners boundaryTable01 x ≠ [] := by
  rw [support_exact]
  decide

theorem boundaryTable01_structure :
    Structure (tableOwners boundaryTable01) 0 boundaryNeighbors01 := by decide

#print axioms boundaryTable01_structure
end SpectreFinite.HexSearch.ParentBoundary
