module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.ParentBoundaryTable05

@[expose] public section


/-! Exact finite neighboring frames and complete native macro-side interfaces. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def boundaryFrames11 : List FrameInfo := [⟨((-3),3),0,1,3⟩,⟨((-3),1),5,2,5⟩,⟨(0,(-2)),4,3,1⟩,⟨(2,(-2)),5,6,1⟩,⟨(3,(-1)),1,1,0⟩,⟨(1,2),2,4,0⟩]

theorem boundaryFrames11_geometry :
    FrameGeometry 0 boundaryNeighbors05 boundaryFrames11 := by decide

#print axioms boundaryFrames11_geometry
end SpectreFinite.HexSearch.ParentBoundary
