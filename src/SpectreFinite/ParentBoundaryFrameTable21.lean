module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable06

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames21 : List FrameInfo := [⟨((-2),2),1,1,2⟩,⟨((-3),1),5,6,5⟩,⟨(1,(-3)),3,8,2⟩,⟨(4,(-4)),2,1,4⟩,⟨(4,(-1)),2,4,5⟩,⟨(1,2),1,5,1⟩]

theorem boundaryFrames21_geometry :
    FrameGeometry 7 boundaryNeighbors06 boundaryFrames21 := by decide

#print axioms boundaryFrames21_geometry
end SpectreFinite.HexSearch.ParentBoundary
