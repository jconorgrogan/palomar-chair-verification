module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable10

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames24 : List FrameInfo := [⟨((-2),3),4,0,5⟩,⟨((-3),1),5,1,5⟩,⟨(1,(-3)),3,7,2⟩,⟨(3,(-3)),5,0,1⟩,⟨(3,0),5,5,2⟩,⟨(1,3),4,3,4⟩]

theorem boundaryFrames24_geometry :
    FrameGeometry 4 boundaryNeighbors10 boundaryFrames24 := by decide

#print axioms boundaryFrames24_geometry
end SpectreFinite.HexSearch.ParentBoundary
