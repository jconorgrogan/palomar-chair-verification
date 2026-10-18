module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable10

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames29 : List FrameInfo := [⟨((-2),3),4,0,5⟩,⟨((-3),1),5,1,5⟩,⟨(1,(-3)),3,7,2⟩,⟨(3,(-3)),5,0,1⟩,⟨(3,0),5,5,2⟩,⟨(1,3),4,1,4⟩]

theorem boundaryFrames29_geometry :
    FrameGeometry 4 boundaryNeighbors10 boundaryFrames29 := by decide

#print axioms boundaryFrames29_geometry
end SpectreFinite.HexSearch.ParentBoundary
