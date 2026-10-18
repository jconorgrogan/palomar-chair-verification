module

public import SpectreFinite.RadiusTwoRoot8Part2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root8Node21Domains0 : Domains 19 State := restrict root8Node17Domains0 12 (6,2)
def root8Node21Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(8,1)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(5,5)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(6,0)]
theorem root8Node21Step1_checked :
    checkReplacement table12 root8Node21Domains0 root8Node21Domains1 = true := by decide
def root8Node21Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(8,1)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(5,5)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(6,0)]
theorem root8Node21Step2_checked :
    checkReplacement table13 root8Node21Domains1 root8Node21Domains2 = true := by decide
def root8Node22Domains0 : Domains 19 State := restrict root8Node21Domains2 7 (3,3)
theorem root8Node22Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node22Domains0 (.output 10) = true := by decide
def root8Node23Domains0 : Domains 19 State := restrict root8Node21Domains2 7 (7,3)
theorem root8Node23Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node23Domains0 (.output 11) = true := by decide
def root8Node24Domains0 : Domains 19 State := restrict root8Node0Domains5 5 (7,1)
def root8Node24Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(4,1),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3),(6,0)]
theorem root8Node24Step1_checked :
    checkReplacement table10 root8Node24Domains0 root8Node24Domains1 = true := by decide
def root8Node24Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(1,3),(3,3),(7,3)]
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
  | _ => [(0,3),(6,0)]
theorem root8Node24Step2_checked :
    checkReplacement table4 root8Node24Domains1 root8Node24Domains2 = true := by decide
def root8Node24Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(1,3),(3,3),(7,3)]
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
  | _ => [(0,3),(6,0)]
theorem root8Node24Step3_checked :
    checkReplacement table1 root8Node24Domains2 root8Node24Domains3 = true := by decide
def root8Node24Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
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
  | _ => [(0,3),(6,0)]
theorem root8Node24Step4_checked :
    checkReplacement table3 root8Node24Domains3 root8Node24Domains4 = true := by decide
def root8Node24Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
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
theorem root8Node24Step5_checked :
    checkReplacement table14 root8Node24Domains4 root8Node24Domains5 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
