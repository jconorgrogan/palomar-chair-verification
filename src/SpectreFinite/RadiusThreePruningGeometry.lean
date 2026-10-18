module

public import SpectreFinite.LargerWindowPruning

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def samples0 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-2,3),(-1,-1),(3,-3),(3,0)]
  | 1 => [(-3,1),(1,-2),(3,-1),(3,0)]
  | 2 => [(-1,-2),(0,3),(2,-1),(2,1)]
  | 3 => [(-3,3),(0,2),(2,-3),(2,0)]
  | 4 => [(-3,0),(-1,2),(0,-1),(3,-1)]
  | _ => [(-1,-1),(-1,2),(0,-3),(1,2)]
theorem samples0_shared : ∀ d : Fin 6, ∀ x ∈ samples0 d, x ∈ hexRegion 3 ∧ addPos (direction d) x ∈ hexRegion 3 := by decide
def samples1 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-2,0),(-2,3),(1,-3),(3,-2),(3,0)]
  | 1 => [(-1,-1),(-1,2),(0,-2),(3,-2)]
  | 2 => [(1,-2),(1,2),(2,-2),(2,1)]
  | 3 => [(-1,3),(0,0),(2,-1),(2,0)]
  | 4 => [(-3,2),(0,2),(2,-2),(3,-1)]
  | _ => [(-2,0),(1,2),(3,0)]
theorem samples1_shared : ∀ d : Fin 6, ∀ x ∈ samples1 d, x ∈ hexRegion 3 ∧ addPos (direction d) x ∈ hexRegion 3 := by decide
def samples2 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-2,2),(0,3),(1,-3),(3,-3),(3,0)]
  | 1 => [(2,1),(3,-1)]
  | 2 => [(1,2),(2,-2)]
  | 3 => []
  | 4 => []
  | _ => []
theorem samples2_shared : ∀ d : Fin 6, ∀ x ∈ samples2 d, x ∈ hexRegion 3 ∧ addPos (direction d) x ∈ hexRegion 3 := by decide

end SpectreFinite.HexSearch.RadiusThreePruning
