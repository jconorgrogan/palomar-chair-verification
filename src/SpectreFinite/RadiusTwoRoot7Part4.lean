module

public import SpectreFinite.RadiusTwoRoot7Part3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node20Domains0 : Domains 19 State := restrict root7Node18Domains2 10 (8,3)
def root7Node20Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(5,1),(8,1)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(5,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3),(6,0)]
theorem root7Node20Step1_checked :
    checkReplacement table10 root7Node20Domains0 root7Node20Domains1 = true := by decide
def root7Node20Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(5,1),(8,1)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(5,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(6,0)]
theorem root7Node20Step2_checked :
    checkReplacement table14 root7Node20Domains1 root7Node20Domains2 = true := by decide
def root7Node21Domains0 : Domains 19 State := restrict root7Node20Domains2 6 (5,1)
theorem root7Node21Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node21Domains0 (.output 9) = true := by decide
def root7Node22Domains0 : Domains 19 State := restrict root7Node20Domains2 6 (8,1)
theorem root7Node22Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node22Domains0 (.output 10) = true := by decide
def root7Node23Domains0 : Domains 19 State := restrict root7Node17Domains2 8 (8,5)
def root7Node23Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(5,2),(5,5),(8,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node23Step1_checked :
    checkReplacement table13 root7Node23Domains0 root7Node23Domains1 = true := by decide
def root7Node23Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3),(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node23Step2_checked :
    checkReplacement table15 root7Node23Domains1 root7Node23Domains2 = true := by decide
def root7Node23Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(5,1),(8,1)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3),(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node23Step3_checked :
    checkReplacement table5 root7Node23Domains2 root7Node23Domains3 = true := by decide
def root7Node24Domains0 : Domains 19 State := restrict root7Node23Domains3 6 (5,1)
def root7Node25Domains0 : Domains 19 State := restrict root7Node24Domains0 15 (1,3)
def root7Node25Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(5,1)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | _ => [(6,5)]
theorem root7Node25Step1_checked :
    checkReplacement table14 root7Node25Domains0 root7Node25Domains1 = true := by decide
theorem root7Node25Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node25Domains1 (.output 11) = true := by decide
def root7Node26Domains0 : Domains 19 State := restrict root7Node24Domains0 15 (6,3)
def root7Node26Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(5,1)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | _ => [(0,2)]
theorem root7Node26Step1_checked :
    checkReplacement table14 root7Node26Domains0 root7Node26Domains1 = true := by decide
theorem root7Node26Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node26Domains1 (.output 12) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
