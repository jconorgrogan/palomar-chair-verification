module

public import SpectreFinite.RadiusThreeModel

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root2Outputs : List (List State) := [
  [(8,2),(5,0),(4,5),(7,0),(0,4),(5,4),(0,0),(7,2),(7,4),(7,0),(4,3),(1,5),(6,1),(4,1),(0,2),(4,4),(1,4),(0,5),(2,0),(7,3),(5,2),(8,0),(7,5),(6,0),(3,1),(0,1),(6,2),(8,4),(8,2),(5,0),(4,5),(1,0),(7,1),(8,4),(0,0),(7,2),(4,0)]
]
def root2Family : List Patch := rowsToPatches positions root2Outputs
end SpectreFinite.HexSearch.RadiusThree
