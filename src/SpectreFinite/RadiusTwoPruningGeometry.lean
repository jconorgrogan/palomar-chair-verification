module

public import SpectreFinite.LargerWindowPruning

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def samples (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-1,0),(-1,1),(-1,2),(0,-1),(0,0),(0,1),(0,2),(1,-2),(1,-1),(1,0),(1,1),(2,-2),(2,-1),(2,0)]
  | 1 => [(-2,1),(-2,2),(-1,0),(-1,1),(-1,2),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(1,1),(2,-1),(2,0)]
  | 2 => [(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-1),(0,0),(0,1),(0,2),(1,-1),(1,0),(1,1)]
  | 3 => [(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,-1),(1,0)]
  | 4 => [(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,-1),(1,0),(2,-2),(2,-1)]
  | _ => [(-1,-1),(-1,0),(-1,1),(0,-2),(0,-1),(0,0),(0,1),(1,-2),(1,-1),(1,0),(1,1),(2,-2),(2,-1),(2,0)]

theorem samples_shared : ∀ d : Fin 6, ∀ x ∈ samples d, x ∈ hexRegion 2 ∧ addPos (direction d) x ∈ hexRegion 2 := by decide

end SpectreFinite.HexSearch.RadiusTwoPruning
