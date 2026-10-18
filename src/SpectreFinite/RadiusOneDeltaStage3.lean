module

public import SpectreFinite.RadiusOneDeltaStage3Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def deltaStage3 : List (List (Position × State)) := [[((1,-1),(7,2)),((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(1,0))],[((1,-1),(8,2)),((0,-1),(4,5)),((-1,0),(0,1)),((0,0),(1,0))],[((1,-1),(4,4)),((0,-1),(5,5)),((-1,0),(0,1)),((0,0),(1,0))],[((1,-1),(7,2)),((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(1,0))],[((1,-1),(8,2)),((0,-1),(8,5)),((-1,0),(0,1)),((0,0),(1,0))],[((1,-1),(7,2)),((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(1,0))],[((1,-1),(8,2)),((0,-1),(4,5)),((-1,0),(1,5)),((0,0),(1,0))],[((1,-1),(4,4)),((0,-1),(5,5)),((-1,0),(1,5)),((0,0),(1,0))],[((1,-1),(7,2)),((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(1,0))],[((1,-1),(8,2)),((0,-1),(8,5)),((-1,0),(1,5)),((0,0),(1,0))],[((1,-1),(7,2)),((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(1,0))],[((1,-1),(8,2)),((0,-1),(4,5)),((-1,0),(6,5)),((0,0),(1,0))],[((1,-1),(4,4)),((0,-1),(5,5)),((-1,0),(6,5)),((0,0),(1,0))],[((1,-1),(7,2)),((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(1,0))],[((1,-1),(8,2)),((0,-1),(8,5)),((-1,0),(6,5)),((0,0),(1,0))]]

theorem deltaStage3_exact : Search.enumerate (choices (1,0)) Matches [(1,-1),(0,-1),(-1,0),(0,0)] = deltaStage3 := by
  rw [enumerate_consRoot, deltaStage2_exact]
  simp only [deltaStage2, List.flatMap_cons, List.flatMap_nil, delta_extend_3_0, delta_extend_3_1, delta_extend_3_2, delta_extend_3_3, delta_extend_3_4, delta_extend_3_5, delta_extend_3_6, delta_extend_3_7, delta_extend_3_8, delta_extend_3_9, delta_extend_3_10, delta_extend_3_11]
  rfl
#print axioms deltaStage3_exact
end SpectreFinite.HexSearch.RadiusOne
