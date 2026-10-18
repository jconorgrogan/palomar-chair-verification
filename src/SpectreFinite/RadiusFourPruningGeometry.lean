module

public import SpectreFinite.LargerWindowPruning

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def samples0 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-3,0),(-3,4),(1,-4),(4,-4),(4,-3),(4,0)]
  | 1 => [(-3,0),(0,-3),(3,1),(4,-3),(4,0)]
  | 2 => [(-1,4),(0,-3),(0,4),(3,-3),(3,1)]
  | 3 => [(-4,3),(-4,4),(-1,4),(3,-3),(3,0)]
  | 4 => [(-4,0),(-4,3),(-3,-1),(0,3),(4,-1)]
  | _ => [(-3,-1),(1,3)]
theorem samples0_shared : ∀ d : Fin 6, ∀ x ∈ samples0 d, x ∈ hexRegion 4 ∧ addPos (direction d) x ∈ hexRegion 4 := by decide

end SpectreFinite.HexSearch.RadiusFourPruning
