module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable07

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames20 : List FrameInfo := [⟨((-2),2),1,1,2⟩,⟨((-3),1),5,6,5⟩,⟨(1,(-3)),3,8,2⟩,⟨(4,(-4)),2,7,4⟩,⟨(4,0),4,7,3⟩,⟨(1,2),1,8,1⟩]

theorem boundaryFrames20_geometry :
    FrameGeometry 7 boundaryNeighbors07 boundaryFrames20 := by decide

#print axioms boundaryFrames20_geometry
end SpectreFinite.HexSearch.ParentBoundary
