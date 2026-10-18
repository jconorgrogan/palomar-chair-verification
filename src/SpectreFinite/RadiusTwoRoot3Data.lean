module

public import SpectreFinite.RadiusTwoTables

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root3Outputs : List (List State) := [
  [(7,4),(1,3),(4,2),(8,1),(6,5),(0,4),(1,4),(5,3),(5,5),(3,0),(2,5),(6,0),(0,5),(4,4),(0,0),(7,2),(7,1),(1,5),(6,1)],
  [(7,4),(1,3),(4,2),(8,1),(6,5),(0,4),(1,4),(8,3),(5,5),(3,0),(2,5),(6,0),(0,5),(4,4),(0,0),(7,2),(7,1),(1,5),(6,1)],
  [(7,4),(1,3),(4,2),(8,1),(6,5),(0,4),(6,4),(5,3),(5,5),(3,0),(2,5),(0,3),(0,5),(4,4),(0,0),(2,2),(7,1),(1,5),(6,1)],
  [(7,4),(1,3),(4,2),(8,1),(6,5),(0,4),(6,4),(8,3),(5,5),(3,0),(2,5),(0,3),(0,5),(4,4),(0,0),(2,2),(7,1),(1,5),(6,1)]
]
def root3Family : List Patch := rowsToPatches positions root3Outputs
end SpectreFinite.HexSearch.RadiusTwo
