module

public import SpectreFinite.RadiusTwoRoot1Part7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root1Node34Domains0 : Domains 19 State := restrict root1Node32Domains1 12 (6,3)
def root1Node34Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | _ => [(0,1),(6,4)]
theorem root1Node34Step1_checked :
    checkReplacement table13 root1Node34Domains0 root1Node34Domains1 = true := by decide
def root1Node34Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root1Node34Step2_checked :
    checkReplacement table14 root1Node34Domains1 root1Node34Domains2 = true := by decide
theorem root1Node34Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node34Domains2 (.output 17) = true := by decide
def root1Node35Domains0 : Domains 19 State := restrict root1Node29Domains0 7 (8,3)
def root1Node36Domains0 : Domains 19 State := restrict root1Node35Domains0 11 (1,5)
def root1Node36Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,0)]
theorem root1Node36Step1_checked :
    checkReplacement table15 root1Node36Domains0 root1Node36Domains1 = true := by decide
def root1Node36Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,0)]
theorem root1Node36Step2_checked :
    checkReplacement table13 root1Node36Domains1 root1Node36Domains2 = true := by decide
theorem root1Node36Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node36Domains2 (.output 18) = true := by decide
def root1Node37Domains0 : Domains 19 State := restrict root1Node35Domains0 11 (7,5)
def root1Node37Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,1),(6,4)]
theorem root1Node37Step1_checked :
    checkReplacement table15 root1Node37Domains0 root1Node37Domains1 = true := by decide
def root1Node38Domains0 : Domains 19 State := restrict root1Node37Domains1 12 (1,3)
def root1Node38Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,1),(6,4)]
theorem root1Node38Step1_checked :
    checkReplacement table13 root1Node38Domains0 root1Node38Domains1 = true := by decide
def root1Node38Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(6,4)]
theorem root1Node38Step2_checked :
    checkReplacement table14 root1Node38Domains1 root1Node38Domains2 = true := by decide
theorem root1Node38Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node38Domains2 (.output 19) = true := by decide
def root1Node39Domains0 : Domains 19 State := restrict root1Node37Domains1 12 (6,3)
def root1Node39Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | _ => [(0,1),(6,4)]
theorem root1Node39Step1_checked :
    checkReplacement table13 root1Node39Domains0 root1Node39Domains1 = true := by decide
def root1Node39Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root1Node39Step2_checked :
    checkReplacement table14 root1Node39Domains1 root1Node39Domains2 = true := by decide
theorem root1Node39Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node39Domains2 (.output 20) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
