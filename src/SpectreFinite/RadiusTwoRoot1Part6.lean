module

public import SpectreFinite.RadiusTwoRoot1Part5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root1Node22Domains0 : Domains 19 State := restrict root1Node21Domains1 12 (1,3)
def root1Node22Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3)]
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
theorem root1Node22Step1_checked :
    checkReplacement table13 root1Node22Domains0 root1Node22Domains1 = true := by decide
def root1Node22Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3)]
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
theorem root1Node22Step2_checked :
    checkReplacement table14 root1Node22Domains1 root1Node22Domains2 = true := by decide
theorem root1Node22Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node22Domains2 (.output 10) = true := by decide
def root1Node23Domains0 : Domains 19 State := restrict root1Node21Domains1 12 (6,3)
def root1Node23Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
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
theorem root1Node23Step1_checked :
    checkReplacement table13 root1Node23Domains0 root1Node23Domains1 = true := by decide
def root1Node23Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
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
theorem root1Node23Step2_checked :
    checkReplacement table14 root1Node23Domains1 root1Node23Domains2 = true := by decide
theorem root1Node23Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node23Domains2 (.output 11) = true := by decide
def root1Node24Domains0 : Domains 19 State := restrict root1Node18Domains0 7 (8,3)
def root1Node25Domains0 : Domains 19 State := restrict root1Node24Domains0 11 (1,5)
def root1Node25Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
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
theorem root1Node25Step1_checked :
    checkReplacement table15 root1Node25Domains0 root1Node25Domains1 = true := by decide
def root1Node25Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
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
theorem root1Node25Step2_checked :
    checkReplacement table13 root1Node25Domains1 root1Node25Domains2 = true := by decide
theorem root1Node25Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node25Domains2 (.output 12) = true := by decide
def root1Node26Domains0 : Domains 19 State := restrict root1Node24Domains0 11 (7,5)
def root1Node26Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
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
theorem root1Node26Step1_checked :
    checkReplacement table15 root1Node26Domains0 root1Node26Domains1 = true := by decide
def root1Node27Domains0 : Domains 19 State := restrict root1Node26Domains1 12 (1,3)
def root1Node27Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
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
theorem root1Node27Step1_checked :
    checkReplacement table13 root1Node27Domains0 root1Node27Domains1 = true := by decide
def root1Node27Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
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
theorem root1Node27Step2_checked :
    checkReplacement table14 root1Node27Domains1 root1Node27Domains2 = true := by decide
theorem root1Node27Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node27Domains2 (.output 13) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
