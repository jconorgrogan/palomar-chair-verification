module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable11

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames26 : List FrameInfo := [⟨((-2),3),4,0,5⟩,⟨((-3),1),5,1,5⟩,⟨(1,(-3)),3,7,2⟩,⟨(4,(-4)),2,6,4⟩,⟨(4,(-1)),2,8,5⟩,⟨(1,3),4,5,4⟩]

theorem boundaryFrames26_geometry :
    FrameGeometry 8 boundaryNeighbors11 boundaryFrames26 := by decide

#print axioms boundaryFrames26_geometry
end SpectreFinite.HexSearch.ParentBoundary
