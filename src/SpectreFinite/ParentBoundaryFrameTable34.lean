module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable13

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames34 : List FrameInfo := [⟨((-2),2),1,6,2⟩,⟨((-2),0),2,0,2⟩,⟨(1,(-3)),3,4,2⟩,⟨(4,(-4)),2,1,4⟩,⟨(4,(-1)),2,4,5⟩,⟨(1,2),1,5,1⟩]

theorem boundaryFrames34_geometry :
    FrameGeometry 7 boundaryNeighbors13 boundaryFrames34 := by decide

#print axioms boundaryFrames34_geometry
end SpectreFinite.HexSearch.ParentBoundary
