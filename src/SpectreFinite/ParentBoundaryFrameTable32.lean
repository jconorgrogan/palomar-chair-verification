module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable14

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames32 : List FrameInfo := [⟨((-2),2),1,6,2⟩,⟨((-2),0),2,0,2⟩,⟨(1,(-3)),3,4,2⟩,⟨(4,(-4)),2,7,4⟩,⟨(4,0),4,7,3⟩,⟨(1,2),1,4,1⟩]

theorem boundaryFrames32_geometry :
    FrameGeometry 7 boundaryNeighbors14 boundaryFrames32 := by decide

#print axioms boundaryFrames32_geometry
end SpectreFinite.HexSearch.ParentBoundary
