module

public import SpectreFinite.LargerWindowPruning

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def samples0 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-4,5),(-2,5),(0,-4),(1,3),(2,3),(4,1),(5,-5),(5,0)]
  | 1 => [(-5,2),(-5,4),(-2,-2),(1,3),(5,-4),(5,0)]
  | 2 => [(-1,-4),(0,5),(2,-3),(4,1)]
  | 3 => [(-5,5),(1,2),(3,-5),(4,-5),(4,-3)]
  | 4 => [(-5,0),(4,-5),(4,0),(5,-1)]
  | _ => [(0,-5),(1,3),(2,3),(4,1),(5,0)]
theorem samples0_shared : ∀ d : Fin 6, ∀ x ∈ samples0 d, x ∈ hexRegion 5 ∧ addPos (direction d) x ∈ hexRegion 5 := by decide
def samples1 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-4,5),(-2,5),(0,-4),(1,3),(3,-4),(5,-5),(5,0)]
  | 1 => [(-5,1),(-5,3),(-1,5),(4,-4),(4,1),(5,-2)]
  | 2 => [(-4,2),(-3,-2),(-1,-4),(-1,5),(2,3),(3,-4),(4,1)]
  | 3 => [(-4,2),(-3,5),(0,-4),(0,4),(2,-5),(4,-5),(4,-1)]
  | 4 => [(-5,2),(0,-4),(1,3),(4,0),(5,-5),(5,-3),(5,-1)]
  | _ => [(0,-5),(0,4),(1,4),(3,2),(5,-5),(5,0)]
theorem samples1_shared : ∀ d : Fin 6, ∀ x ∈ samples1 d, x ∈ hexRegion 5 ∧ addPos (direction d) x ∈ hexRegion 5 := by decide
def samples2 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-3,5),(-1,-3),(0,3),(0,4),(0,5),(2,-4),(2,3),(4,-5),(5,-3),(5,0)]
  | 1 => [(-5,2),(-5,5),(1,4),(2,-4),(4,-4),(5,-2)]
  | 2 => [(-5,0),(-2,-3),(-2,5),(2,3),(3,-3),(4,0)]
  | 3 => [(-5,3),(-2,5),(0,-5),(1,1),(2,-2),(3,-5)]
  | 4 => [(-5,3),(-1,-4),(-1,2),(5,-5),(5,-3),(5,-2)]
  | _ => [(-1,-4),(-1,2),(2,3),(4,-5),(5,-3),(5,0)]
theorem samples2_shared : ∀ d : Fin 6, ∀ x ∈ samples2 d, x ∈ hexRegion 5 ∧ addPos (direction d) x ∈ hexRegion 5 := by decide
def samples3 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-4,5),(-2,-2),(-1,3),(-1,4),(1,-4),(1,4),(3,-5),(4,1),(5,-5),(5,-2)]
  | 1 => [(-5,1),(-4,5),(1,-2),(1,3),(3,-4),(3,2),(5,-2)]
  | 2 => [(-4,-1),(-4,3),(-1,-4),(-1,5),(3,2),(4,-3),(4,-1)]
  | 3 => [(-5,4),(-1,5),(0,-5),(1,3),(3,-2),(3,1),(4,-5),(4,0)]
  | 4 => [(-5,4),(-2,-3),(-2,3),(1,-4),(1,2),(5,-4),(5,-1)]
  | _ => [(-2,-3),(-2,3),(1,4),(3,-5),(5,-4),(5,0)]
theorem samples3_shared : ∀ d : Fin 6, ∀ x ∈ samples3 d, x ∈ hexRegion 5 ∧ addPos (direction d) x ∈ hexRegion 5 := by decide
def samples4 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-4,5),(-3,-1),(-1,4),(0,5),(1,-5),(3,-5),(3,2),(5,-4)]
  | 1 => [(-4,0),(-4,5),(1,4),(3,-4),(5,-4),(5,0)]
  | 2 => [(-4,5),(-3,-2),(0,-4),(1,4),(4,-1),(4,0),(4,1)]
  | 3 => [(-4,4),(-4,5),(-3,-2),(-1,5),(1,-3),(1,3),(2,-5),(4,-4)]
  | 4 => [(-5,4),(-3,-2),(-2,3),(0,-3),(1,3),(5,-3),(5,-1)]
  | _ => [(-4,-1),(-2,3),(2,-5),(5,-4)]
theorem samples4_shared : ∀ d : Fin 6, ∀ x ∈ samples4 d, x ∈ hexRegion 5 ∧ addPos (direction d) x ∈ hexRegion 5 := by decide
def samples5 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-4,5),(-3,-1),(-3,0),(-3,1),(1,-5),(1,4),(3,2),(4,-4),(5,-5),(5,-2)]
  | 1 => [(-5,1),(1,-4),(2,3),(5,-4),(5,-2),(5,0)]
  | 2 => [(-3,5),(-1,-4),(0,5),(3,2),(4,-3),(4,1)]
  | 3 => [(-5,5),(-2,4),(0,-5),(1,3),(3,1),(4,-5)]
  | 4 => [(-3,1),(-3,4),(0,4),(1,1),(5,-3),(5,-1)]
  | _ => [(-3,1),(-3,4),(1,4),(5,-3)]
theorem samples5_shared : ∀ d : Fin 6, ∀ x ∈ samples5 d, x ∈ hexRegion 5 ∧ addPos (direction d) x ∈ hexRegion 5 := by decide
def samples6 (d : Fin 6) : List Position :=
  match d.val with
  | 0 => [(-4,0),(-4,1),(-4,2),(-4,3),(-4,4),(-4,5),(-3,-1),(-2,-2),(-1,-3),(0,-4),(1,-5),(5,0)]
  | 1 => [(-2,-2),(0,-4),(1,-4),(2,-4),(3,-4),(4,-4),(4,1),(5,-4),(5,-2)]
  | 2 => [(1,1),(1,4),(2,-4),(4,-4),(4,-3),(4,-2),(4,-1),(4,0),(4,1)]
  | 3 => [(-2,5),(-1,5),(0,4),(1,3),(2,2),(3,-5),(3,1),(4,-2),(4,0)]
  | 4 => [(-5,4),(-4,4),(-3,4),(-2,4),(-1,4),(0,4),(1,-5),(5,-1)]
  | _ => [(-4,2),(1,4),(5,-1)]
theorem samples6_shared : ∀ d : Fin 6, ∀ x ∈ samples6 d, x ∈ hexRegion 5 ∧ addPos (direction d) x ∈ hexRegion 5 := by decide

end SpectreFinite.HexSearch.RadiusFivePruning
