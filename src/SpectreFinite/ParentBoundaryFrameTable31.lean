module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable13

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames31 : List FrameInfo := [⟨((-2),2),1,6,2⟩,⟨((-2),0),2,0,2⟩,⟨(1,(-3)),3,2,2⟩,⟨(4,(-4)),2,6,4⟩,⟨(4,(-1)),2,4,5⟩,⟨(1,2),1,5,1⟩]

theorem boundaryFrames31_geometry :
    FrameGeometry 7 boundaryNeighbors13 boundaryFrames31 := by decide

#print axioms boundaryFrames31_geometry
end SpectreFinite.HexSearch.ParentBoundary
