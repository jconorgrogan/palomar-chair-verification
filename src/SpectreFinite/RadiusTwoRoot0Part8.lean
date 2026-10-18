module

public import SpectreFinite.RadiusTwoRoot0Part7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node34Domains0 : Domains 19 State := restrict root0Node33Domains0 8 (5,4)
def root0Node34Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(4,3)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(0,5)]
  | 17 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node34Step1_checked :
    checkReplacement table12 root0Node34Domains0 root0Node34Domains1 = true := by decide
def root0Node34Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(4,3)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(0,5)]
  | 17 => [(2,0)]
  | _ => [(7,3)]
theorem root0Node34Step2_checked :
    checkReplacement table17 root0Node34Domains1 root0Node34Domains2 = true := by decide
def root0Node34Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(4,3)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1)]
  | 16 => [(0,5)]
  | 17 => [(2,0)]
  | _ => [(7,3)]
theorem root0Node34Step3_checked :
    checkReplacement table14 root0Node34Domains2 root0Node34Domains3 = true := by decide
theorem root0Node34Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node34Domains3 (.output 17) = true := by decide
def root0Node35Domains0 : Domains 19 State := restrict root0Node33Domains0 8 (8,4)
def root0Node35Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(1,2),(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node35Step1_checked :
    checkReplacement table12 root0Node35Domains0 root0Node35Domains1 = true := by decide
def root0Node35Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(1,2),(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(4,5),(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node35Step2_checked :
    checkReplacement table13 root0Node35Domains1 root0Node35Domains2 = true := by decide
def root0Node36Domains0 : Domains 19 State := restrict root0Node35Domains2 7 (1,2)
def root0Node36Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(1,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node36Step1_checked :
    checkReplacement table12 root0Node36Domains0 root0Node36Domains1 = true := by decide
def root0Node37Domains0 : Domains 19 State := restrict root0Node36Domains1 15 (4,1)
def root0Node37Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(1,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1)]
  | 16 => [(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(7,3)]
theorem root0Node37Step1_checked :
    checkReplacement table14 root0Node37Domains0 root0Node37Domains1 = true := by decide
def root0Node37Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(1,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1)]
  | 16 => [(5,5)]
  | 17 => [(7,0)]
  | _ => [(7,3)]
theorem root0Node37Step2_checked :
    checkReplacement table17 root0Node37Domains1 root0Node37Domains2 = true := by decide
theorem root0Node37Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node37Domains2 (.output 18) = true := by decide
def root0Node38Domains0 : Domains 19 State := restrict root0Node36Domains1 15 (8,1)
def root0Node38Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(1,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(8,1)]
  | 16 => [(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node38Step1_checked :
    checkReplacement table14 root0Node38Domains0 root0Node38Domains1 = true := by decide
def root0Node39Domains0 : Domains 19 State := restrict root0Node38Domains1 16 (5,5)
theorem root0Node39Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node39Domains0 (.output 19) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
