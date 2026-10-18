module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable01

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames05 : List FrameInfo := [⟨((-3),3),0,3,3⟩,⟨((-3),0),1,2,3⟩,⟨(0,(-2)),4,7,1⟩,⟨(2,(-2)),5,6,1⟩,⟨(3,(-1)),1,1,0⟩,⟨(1,2),2,4,0⟩]

theorem boundaryFrames05_geometry :
    FrameGeometry 0 boundaryNeighbors01 boundaryFrames05 := by decide

#print axioms boundaryFrames05_geometry
end SpectreFinite.HexSearch.ParentBoundary
