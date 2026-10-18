module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable02

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames12 : List FrameInfo := [⟨((-3),3),0,1,3⟩,⟨((-3),1),5,7,5⟩,⟨(0,(-3)),1,4,4⟩,⟨(3,(-3)),0,0,0⟩,⟨(4,(-1)),2,5,5⟩,⟨(1,3),4,8,4⟩]

theorem boundaryFrames12_geometry :
    FrameGeometry 5 boundaryNeighbors02 boundaryFrames12 := by decide

#print axioms boundaryFrames12_geometry
end SpectreFinite.HexSearch.ParentBoundary
