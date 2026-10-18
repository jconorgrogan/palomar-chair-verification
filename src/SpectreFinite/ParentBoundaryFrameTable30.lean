module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable12

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames30 : List FrameInfo := [⟨((-2),2),1,6,2⟩,⟨((-2),0),2,0,2⟩,⟨(0,(-3)),1,2,4⟩,⟨(3,(-3)),0,0,0⟩,⟨(4,(-1)),2,4,5⟩,⟨(1,2),1,5,1⟩]

theorem boundaryFrames30_geometry :
    FrameGeometry 3 boundaryNeighbors12 boundaryFrames30 := by decide

#print axioms boundaryFrames30_geometry
end SpectreFinite.HexSearch.ParentBoundary
