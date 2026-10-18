module

public import SpectreFinite.RadiusTwoRoot6Part5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root6Node33Domains0 : Domains 19 State := restrict root6Node29Domains3 11 (7,5)
def root6Node33Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(6,4)]
theorem root6Node33Step1_checked :
    checkReplacement table15 root6Node33Domains0 root6Node33Domains1 = true := by decide
def root6Node33Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | _ => [(6,4)]
theorem root6Node33Step2_checked :
    checkReplacement table13 root6Node33Domains1 root6Node33Domains2 = true := by decide
theorem root6Node33Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node33Domains2 (.output 17) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
