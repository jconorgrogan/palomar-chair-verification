module

public import SpectreFinite.RadiusTwoRoot0Part8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node40Domains0 : Domains 19 State := restrict root0Node38Domains1 16 (8,5)
theorem root0Node40Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node40Domains0 (.output 20) = true := by decide
def root0Node41Domains0 : Domains 19 State := restrict root0Node35Domains2 7 (6,2)
def root0Node41Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node41Step1_checked :
    checkReplacement table12 root0Node41Domains0 root0Node41Domains1 = true := by decide
def root0Node41Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node41Step2_checked :
    checkReplacement table17 root0Node41Domains1 root0Node41Domains2 = true := by decide
def root0Node41Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(8,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node41Step3_checked :
    checkReplacement table14 root0Node41Domains2 root0Node41Domains3 = true := by decide
theorem root0Node41Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node41Domains3 (.output 21) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
