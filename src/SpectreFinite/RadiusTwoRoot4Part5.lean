module

public import SpectreFinite.RadiusTwoRoot4Part4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root4Node32Domains0 : Domains 19 State := restrict root4Node24Domains2 3 (7,5)
def root4Node32Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node32Step1_checked :
    checkReplacement table7 root4Node32Domains0 root4Node32Domains1 = true := by decide
def root4Node32Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | _ => [(1,0)]
theorem root4Node32Step2_checked :
    checkReplacement table13 root4Node32Domains1 root4Node32Domains2 = true := by decide
def root4Node33Domains0 : Domains 19 State := restrict root4Node32Domains2 11 (4,2)
theorem root4Node33Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node33Domains0 (.output 16) = true := by decide
def root4Node34Domains0 : Domains 19 State := restrict root4Node32Domains2 11 (8,2)
theorem root4Node34Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node34Domains0 (.output 17) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
