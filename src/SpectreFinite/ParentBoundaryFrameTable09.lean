module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable04

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames09 : List FrameInfo := [⟨((-3),3),0,6,3⟩,⟨((-3),1),5,7,5⟩,⟨(1,(-3)),3,7,2⟩,⟨(4,(-4)),2,6,4⟩,⟨(4,(-1)),2,5,5⟩,⟨(1,3),4,8,4⟩]

theorem boundaryFrames09_geometry :
    FrameGeometry 8 boundaryNeighbors04 boundaryFrames09 := by decide

#print axioms boundaryFrames09_geometry
end SpectreFinite.HexSearch.ParentBoundary
