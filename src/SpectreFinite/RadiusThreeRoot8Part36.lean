module

public import SpectreFinite.RadiusThreeRoot8Part35
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node74Domains0 : Domains 37 State := restrict root8Node72Domains1 33 (8,0)
def root8Node74Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(6,4)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node74Domains0_fast_eq : root8Node74Domains0 = expandDomains root8Node74Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node74Domains0 v = expandDomains root8Node74Domains0Fast v from by decide) v
theorem root8Node74Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node74Domains0 (.output 37) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
