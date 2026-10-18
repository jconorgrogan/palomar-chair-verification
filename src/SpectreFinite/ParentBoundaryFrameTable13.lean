module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable03

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames13 : List FrameInfo := [⟨((-3),3),0,1,3⟩,⟨((-3),1),5,7,5⟩,⟨(1,(-3)),3,7,2⟩,⟨(3,(-3)),5,0,1⟩,⟨(3,0),5,5,2⟩,⟨(1,3),4,7,4⟩]

theorem boundaryFrames13_geometry :
    FrameGeometry 4 boundaryNeighbors03 boundaryFrames13 := by decide

#print axioms boundaryFrames13_geometry
end SpectreFinite.HexSearch.ParentBoundary
