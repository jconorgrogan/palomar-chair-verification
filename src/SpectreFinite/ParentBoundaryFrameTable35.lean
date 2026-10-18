module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable15

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames35 : List FrameInfo := [⟨((-2),3),5,0,4⟩,⟨((-2),1),4,6,0⟩,⟨(0,(-2)),5,7,0⟩,⟨(3,(-3)),0,4,0⟩,⟨(4,0),4,7,3⟩,⟨(1,2),1,4,1⟩]

theorem boundaryFrames35_geometry :
    FrameGeometry 1 boundaryNeighbors15 boundaryFrames35 := by decide

#print axioms boundaryFrames35_geometry
end SpectreFinite.HexSearch.ParentBoundary
