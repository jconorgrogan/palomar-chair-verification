module

public import SpectreFinite.RadiusTwoRoot6Part3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root6Node23Domains0 : Domains 19 State := restrict root6Node0Domains4 0 (8,0)
def root6Node23Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(0,4),(4,4),(5,4),(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(3,0),(4,3),(7,1)]
  | 8 => [(2,5),(3,5),(7,5)]
  | 9 => [(6,0)]
  | 10 => [(2,1),(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(1,2),(6,1),(6,2),(7,1)]
  | 17 => [(1,5),(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root6Node23Step1_checked :
    checkReplacement table1 root6Node23Domains0 root6Node23Domains1 = true := by decide
def root6Node23Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(0,4),(4,4),(5,4),(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(3,0),(4,3),(7,1)]
  | 8 => [(2,5),(3,5),(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(1,2),(6,1),(6,2),(7,1)]
  | 17 => [(1,5),(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root6Node23Step2_checked :
    checkReplacement table6 root6Node23Domains1 root6Node23Domains2 = true := by decide
def root6Node23Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(0,4),(4,4),(5,4),(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(3,0),(4,3),(7,1)]
  | 8 => [(2,5),(3,5),(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(1,2),(6,1),(6,2),(7,1)]
  | 17 => [(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,4)]
theorem root6Node23Step3_checked :
    checkReplacement table14 root6Node23Domains2 root6Node23Domains3 = true := by decide
def root6Node23Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4),(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3),(7,1)]
  | 8 => [(3,5),(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(1,2),(6,1),(6,2),(7,1)]
  | 17 => [(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,4)]
theorem root6Node23Step4_checked :
    checkReplacement table3 root6Node23Domains3 root6Node23Domains4 = true := by decide
def root6Node23Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4),(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3),(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(1,3),(6,3),(7,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(1,2),(6,2)]
  | 17 => [(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,4)]
theorem root6Node23Step5_checked :
    checkReplacement table12 root6Node23Domains4 root6Node23Domains5 = true := by decide
def root6Node24Domains0 : Domains 19 State := restrict root6Node23Domains5 3 (5,4)
def root6Node24Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(1,2),(6,2)]
  | 17 => [(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,4)]
theorem root6Node24Step1_checked :
    checkReplacement table7 root6Node24Domains0 root6Node24Domains1 = true := by decide
def root6Node24Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,4)]
theorem root6Node24Step2_checked :
    checkReplacement table13 root6Node24Domains1 root6Node24Domains2 = true := by decide
def root6Node25Domains0 : Domains 19 State := restrict root6Node24Domains2 11 (1,5)
def root6Node25Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,0)]
theorem root6Node25Step1_checked :
    checkReplacement table15 root6Node25Domains0 root6Node25Domains1 = true := by decide
def root6Node25Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,0)]
theorem root6Node25Step2_checked :
    checkReplacement table13 root6Node25Domains1 root6Node25Domains2 = true := by decide
theorem root6Node25Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node25Domains2 (.output 12) = true := by decide
def root6Node26Domains0 : Domains 19 State := restrict root6Node24Domains2 11 (7,5)
def root6Node26Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,1),(6,4)]
theorem root6Node26Step1_checked :
    checkReplacement table15 root6Node26Domains0 root6Node26Domains1 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
