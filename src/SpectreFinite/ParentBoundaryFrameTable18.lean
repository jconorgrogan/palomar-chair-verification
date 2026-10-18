module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable06

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames18 : List FrameInfo := [⟨((-2),2),1,1,2⟩,⟨((-3),1),5,6,5⟩,⟨(1,(-3)),3,7,2⟩,⟨(4,(-4)),2,6,4⟩,⟨(4,(-1)),2,4,5⟩,⟨(1,2),1,5,1⟩]

theorem boundaryFrames18_geometry :
    FrameGeometry 7 boundaryNeighbors06 boundaryFrames18 := by decide

#print axioms boundaryFrames18_geometry
end SpectreFinite.HexSearch.ParentBoundary
