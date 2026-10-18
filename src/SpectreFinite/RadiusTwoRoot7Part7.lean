module

public import SpectreFinite.RadiusTwoRoot7Part6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node37Domains0 : Domains 19 State := restrict root7Node33Domains4 7 (8,3)
def root7Node38Domains0 : Domains 19 State := restrict root7Node37Domains0 10 (2,3)
def root7Node38Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3)]
  | 11 => [(0,2)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3)]
theorem root7Node38Step1_checked :
    checkReplacement table15 root7Node38Domains0 root7Node38Domains1 = true := by decide
theorem root7Node38Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node38Domains1 (.output 18) = true := by decide
def root7Node39Domains0 : Domains 19 State := restrict root7Node37Domains0 10 (4,3)
def root7Node39Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(6,0)]
theorem root7Node39Step1_checked :
    checkReplacement table15 root7Node39Domains0 root7Node39Domains1 = true := by decide
theorem root7Node39Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node39Domains1 (.output 19) = true := by decide
def root7Node40Domains0 : Domains 19 State := restrict root7Node32Domains1 2 (8,2)
def root7Node40Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5),(3,5),(7,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node40Step1_checked :
    checkReplacement table6 root7Node40Domains0 root7Node40Domains1 = true := by decide
def root7Node40Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5),(3,5),(7,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(7,4)]
  | 15 => [(0,5),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
theorem root7Node40Step2_checked :
    checkReplacement table14 root7Node40Domains1 root7Node40Domains2 = true := by decide
def root7Node41Domains0 : Domains 19 State := restrict root7Node40Domains2 3 (7,1)
def root7Node41Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5),(3,5),(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(1,4),(7,4)]
  | 15 => [(0,5),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
theorem root7Node41Step1_checked :
    checkReplacement table8 root7Node41Domains0 root7Node41Domains1 = true := by decide
def root7Node41Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5),(3,5),(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(0,5),(1,3),(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
theorem root7Node41Step2_checked :
    checkReplacement table13 root7Node41Domains1 root7Node41Domains2 = true := by decide
def root7Node41Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3),(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node41Step3_checked :
    checkReplacement table15 root7Node41Domains2 root7Node41Domains3 = true := by decide
def root7Node42Domains0 : Domains 19 State := restrict root7Node41Domains3 15 (1,3)
def root7Node42Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | _ => [(6,5)]
theorem root7Node42Step1_checked :
    checkReplacement table14 root7Node42Domains0 root7Node42Domains1 = true := by decide
theorem root7Node42Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node42Domains1 (.output 20) = true := by decide
def root7Node43Domains0 : Domains 19 State := restrict root7Node41Domains3 15 (6,3)
def root7Node43Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1)]
  | _ => [(0,2)]
theorem root7Node43Step1_checked :
    checkReplacement table14 root7Node43Domains0 root7Node43Domains1 = true := by decide
theorem root7Node43Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node43Domains1 (.output 21) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
