module

public import SpectreFinite.RadiusTwoRoot8Part4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root8Node32Domains0 : Domains 19 State := restrict root8Node24Domains5 0 (1,4)
def root8Node32Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(1,3),(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3)]
theorem root8Node32Step1_checked :
    checkReplacement table0 root8Node32Domains0 root8Node32Domains1 = true := by decide
def root8Node32Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(1,3),(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3)]
theorem root8Node32Step2_checked :
    checkReplacement table1 root8Node32Domains1 root8Node32Domains2 = true := by decide
def root8Node33Domains0 : Domains 19 State := restrict root8Node32Domains2 7 (1,3)
def root8Node33Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(4,3)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3)]
theorem root8Node33Step1_checked :
    checkReplacement table12 root8Node33Domains0 root8Node33Domains1 = true := by decide
def root8Node34Domains0 : Domains 19 State := restrict root8Node33Domains1 11 (4,2)
def root8Node35Domains0 : Domains 19 State := restrict root8Node34Domains0 17 (3,5)
theorem root8Node35Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node35Domains0 (.output 16) = true := by decide
def root8Node36Domains0 : Domains 19 State := restrict root8Node34Domains0 17 (7,5)
theorem root8Node36Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node36Domains0 (.output 17) = true := by decide
def root8Node37Domains0 : Domains 19 State := restrict root8Node33Domains1 11 (8,2)
def root8Node38Domains0 : Domains 19 State := restrict root8Node37Domains0 17 (3,5)
theorem root8Node38Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node38Domains0 (.output 18) = true := by decide
def root8Node39Domains0 : Domains 19 State := restrict root8Node37Domains0 17 (7,5)
theorem root8Node39Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node39Domains0 (.output 19) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
