module

public import SpectreFinite.RadiusThreeRoot2Part1

@[expose] public section
namespace SpectreFinite.HexSearch.RadiusThree.DomainAliasPilot
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def originalFast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(5,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(2,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(8,0)]
  | 22 => some [(7,5)]
  | 23 => some [(6,0)]
  | 24 => some [(3,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(8,2)]
  | 29 => some [(5,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(8,4)]
  | 34 => some [(0,0)]
  | 35 => some [(7,2)]
  | _ => some [(4,0)]

theorem original_fast_equals_actual : originalFast = SpectreFinite.HexSearch.RadiusThree.root2Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, originalFast v = SpectreFinite.HexSearch.RadiusThree.root2Node0Domains4Fast v from by decide) v
end SpectreFinite.HexSearch.RadiusThree.DomainAliasPilot
