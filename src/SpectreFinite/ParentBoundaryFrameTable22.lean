module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable08

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames22 : List FrameInfo := [⟨((-2),2),1,1,2⟩,⟨((-3),1),5,6,5⟩,⟨(1,(-3)),3,7,2⟩,⟨(3,(-3)),5,0,1⟩,⟨(3,0),5,3,2⟩,⟨(1,2),1,0,1⟩]

theorem boundaryFrames22_geometry :
    FrameGeometry 2 boundaryNeighbors08 boundaryFrames22 := by decide

#print axioms boundaryFrames22_geometry
end SpectreFinite.HexSearch.ParentBoundary
