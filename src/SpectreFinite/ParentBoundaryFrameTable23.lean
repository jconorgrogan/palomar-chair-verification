module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable09

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames23 : List FrameInfo := [⟨((-2),3),4,0,5⟩,⟨((-3),1),5,1,5⟩,⟨(0,(-3)),1,4,4⟩,⟨(3,(-3)),0,0,0⟩,⟨(4,(-1)),2,8,5⟩,⟨(1,3),4,5,4⟩]

theorem boundaryFrames23_geometry :
    FrameGeometry 5 boundaryNeighbors09 boundaryFrames23 := by decide

#print axioms boundaryFrames23_geometry
end SpectreFinite.HexSearch.ParentBoundary
