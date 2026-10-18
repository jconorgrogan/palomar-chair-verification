module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable00

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames03 : List FrameInfo := [⟨((-1),2),2,1,1⟩,⟨((-2),0),1,0,3⟩,⟨(0,(-2)),5,7,0⟩,⟨(3,(-3)),0,8,0⟩,⟨(4,0),4,8,3⟩,⟨(1,2),1,7,1⟩]

theorem boundaryFrames03_geometry :
    FrameGeometry 6 boundaryNeighbors00 boundaryFrames03 := by decide

#print axioms boundaryFrames03_geometry
end SpectreFinite.HexSearch.ParentBoundary
