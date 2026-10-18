module

public import SpectreFinite.RadiusTwoRoot5Part3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root5Node31Domains0 : Domains 19 State := restrict root5Node30Domains1 12 (1,2)
def root5Node31Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(1,5)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node31Step1_checked :
    checkReplacement table12 root5Node31Domains0 root5Node31Domains1 = true := by decide
theorem root5Node31Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node31Domains1 (.output 15) = true := by decide
def root5Node32Domains0 : Domains 19 State := restrict root5Node30Domains1 12 (6,2)
def root5Node32Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(1,5)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node32Step1_checked :
    checkReplacement table12 root5Node32Domains0 root5Node32Domains1 = true := by decide
theorem root5Node32Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node32Domains1 (.output 16) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
