module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable02

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames06 : List FrameInfo := [⟨((-3),3),0,6,3⟩,⟨((-3),1),5,7,5⟩,⟨(0,(-3)),1,4,4⟩,⟨(3,(-3)),0,0,0⟩,⟨(4,(-1)),2,5,5⟩,⟨(1,3),4,8,4⟩]

theorem boundaryFrames06_geometry :
    FrameGeometry 5 boundaryNeighbors02 boundaryFrames06 := by decide

#print axioms boundaryFrames06_geometry
end SpectreFinite.HexSearch.ParentBoundary
