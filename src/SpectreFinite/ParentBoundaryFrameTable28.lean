module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable11

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames28 : List FrameInfo := [⟨((-2),3),4,0,5⟩,⟨((-3),1),5,1,5⟩,⟨(1,(-3)),3,8,2⟩,⟨(4,(-4)),2,1,4⟩,⟨(4,(-1)),2,8,5⟩,⟨(1,3),4,5,4⟩]

theorem boundaryFrames28_geometry :
    FrameGeometry 8 boundaryNeighbors11 boundaryFrames28 := by decide

#print axioms boundaryFrames28_geometry
end SpectreFinite.HexSearch.ParentBoundary
