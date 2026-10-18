module

public import SpectreFinite.RadiusThreeRoot5Part24
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node48Domains0 : Domains 37 State := restrict root5Node46Domains1 34 (8,5)
def root5Node48Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(3,0)]
  | 4 => some [(8,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5)]
  | 14 => some [(6,1)]
  | 15 => some [(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(8,3)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(0,3)]
  | 29 => some [(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(8,1)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node48Domains0_fast_eq : root5Node48Domains0 = expandDomains root5Node48Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node48Domains0 v = expandDomains root5Node48Domains0Fast v from by decide) v
theorem root5Node48Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node48Domains0 (.output 24) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
