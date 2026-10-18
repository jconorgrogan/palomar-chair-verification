module

public import SpectreFinite.RadiusTwoRoot8Part3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root8Node25Domains0 : Domains 19 State := restrict root8Node24Domains5 0 (0,1)
def root8Node25Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
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
theorem root8Node25Step1_checked :
    checkReplacement table0 root8Node25Domains0 root8Node25Domains1 = true := by decide
def root8Node25Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
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
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3)]
theorem root8Node25Step2_checked :
    checkReplacement table8 root8Node25Domains1 root8Node25Domains2 = true := by decide
def root8Node25Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
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
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3)]
theorem root8Node25Step3_checked :
    checkReplacement table1 root8Node25Domains2 root8Node25Domains3 = true := by decide
def root8Node25Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
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
theorem root8Node25Step4_checked :
    checkReplacement table12 root8Node25Domains3 root8Node25Domains4 = true := by decide
def root8Node26Domains0 : Domains 19 State := restrict root8Node25Domains4 11 (4,2)
def root8Node27Domains0 : Domains 19 State := restrict root8Node26Domains0 17 (3,5)
theorem root8Node27Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node27Domains0 (.output 12) = true := by decide
def root8Node28Domains0 : Domains 19 State := restrict root8Node26Domains0 17 (7,5)
theorem root8Node28Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node28Domains0 (.output 13) = true := by decide
def root8Node29Domains0 : Domains 19 State := restrict root8Node25Domains4 11 (8,2)
def root8Node30Domains0 : Domains 19 State := restrict root8Node29Domains0 17 (3,5)
theorem root8Node30Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node30Domains0 (.output 14) = true := by decide
def root8Node31Domains0 : Domains 19 State := restrict root8Node29Domains0 17 (7,5)
theorem root8Node31Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node31Domains0 (.output 15) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
