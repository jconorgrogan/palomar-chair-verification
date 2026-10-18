module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable02

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames17 : List FrameInfo := [⟨((-3),3),0,6,3⟩,⟨((-3),1),5,3,5⟩,⟨(0,(-3)),1,4,4⟩,⟨(3,(-3)),0,0,0⟩,⟨(4,(-1)),2,8,5⟩,⟨(1,3),4,8,4⟩]

theorem boundaryFrames17_geometry :
    FrameGeometry 5 boundaryNeighbors02 boundaryFrames17 := by decide

#print axioms boundaryFrames17_geometry
end SpectreFinite.HexSearch.ParentBoundary
