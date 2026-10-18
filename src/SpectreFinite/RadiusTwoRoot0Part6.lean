module

public import SpectreFinite.RadiusTwoRoot0Part5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node23Domains0 : Domains 19 State := restrict root0Node17Domains0 1 (7,1)
def root0Node23Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5),(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(0,4),(1,2),(6,2)]
  | 8 => [(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0),(7,4)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(5,1),(8,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node23Step1_checked :
    checkReplacement table2 root0Node23Domains0 root0Node23Domains1 = true := by decide
def root0Node23Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5),(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(0,4),(1,2),(6,2)]
  | 8 => [(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node23Step2_checked :
    checkReplacement table10 root0Node23Domains1 root0Node23Domains2 = true := by decide
def root0Node24Domains0 : Domains 19 State := restrict root0Node23Domains2 2 (1,5)
def root0Node25Domains0 : Domains 19 State := restrict root0Node24Domains0 8 (5,4)
def root0Node25Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
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
theorem root0Node25Step1_checked :
    checkReplacement table12 root0Node25Domains0 root0Node25Domains1 = true := by decide
def root0Node25Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
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
theorem root0Node25Step2_checked :
    checkReplacement table17 root0Node25Domains1 root0Node25Domains2 = true := by decide
def root0Node25Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
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
theorem root0Node25Step3_checked :
    checkReplacement table14 root0Node25Domains2 root0Node25Domains3 = true := by decide
theorem root0Node25Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node25Domains3 (.output 12) = true := by decide
def root0Node26Domains0 : Domains 19 State := restrict root0Node24Domains0 8 (8,4)
def root0Node26Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
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
theorem root0Node26Step1_checked :
    checkReplacement table12 root0Node26Domains0 root0Node26Domains1 = true := by decide
def root0Node26Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
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
theorem root0Node26Step2_checked :
    checkReplacement table13 root0Node26Domains1 root0Node26Domains2 = true := by decide
def root0Node27Domains0 : Domains 19 State := restrict root0Node26Domains2 7 (1,2)
def root0Node27Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
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
theorem root0Node27Step1_checked :
    checkReplacement table12 root0Node27Domains0 root0Node27Domains1 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
