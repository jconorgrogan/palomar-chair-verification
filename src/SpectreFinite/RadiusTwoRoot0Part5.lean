module

public import SpectreFinite.RadiusTwoRoot0Part4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node17Domains0 : Domains 19 State := restrict root0Node13Domains1 0 (6,0)
def root0Node18Domains0 : Domains 19 State := restrict root0Node17Domains0 1 (3,1)
def root0Node18Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(3,1)]
  | 2 => [(0,1)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
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
theorem root0Node18Step1_checked :
    checkReplacement table2 root0Node18Domains0 root0Node18Domains1 = true := by decide
def root0Node18Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(3,1)]
  | 2 => [(0,1)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(0,4),(1,2),(6,2)]
  | 8 => [(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node18Step2_checked :
    checkReplacement table10 root0Node18Domains1 root0Node18Domains2 = true := by decide
def root0Node18Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(3,1)]
  | 2 => [(0,1)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(0,4),(1,2),(6,2)]
  | 8 => [(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node18Step3_checked :
    checkReplacement table14 root0Node18Domains2 root0Node18Domains3 = true := by decide
def root0Node18Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(3,1)]
  | 2 => [(0,1)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(0,4),(1,2),(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0)]
  | 12 => [(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(4,5),(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node18Step4_checked :
    checkReplacement table13 root0Node18Domains3 root0Node18Domains4 = true := by decide
def root0Node18Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(3,1)]
  | 2 => [(0,1)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(1,2),(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0)]
  | 12 => [(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(4,5),(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node18Step5_checked :
    checkReplacement table3 root0Node18Domains4 root0Node18Domains5 = true := by decide
def root0Node19Domains0 : Domains 19 State := restrict root0Node18Domains5 7 (1,2)
def root0Node19Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(3,1)]
  | 2 => [(0,1)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(1,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0)]
  | 12 => [(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node19Step1_checked :
    checkReplacement table12 root0Node19Domains0 root0Node19Domains1 = true := by decide
def root0Node20Domains0 : Domains 19 State := restrict root0Node19Domains1 16 (5,5)
theorem root0Node20Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node20Domains0 (.output 9) = true := by decide
def root0Node21Domains0 : Domains 19 State := restrict root0Node19Domains1 16 (8,5)
theorem root0Node21Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node21Domains0 (.output 10) = true := by decide
def root0Node22Domains0 : Domains 19 State := restrict root0Node18Domains5 7 (6,2)
def root0Node22Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(3,1)]
  | 2 => [(0,1)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node22Step1_checked :
    checkReplacement table12 root0Node22Domains0 root0Node22Domains1 = true := by decide
theorem root0Node22Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node22Domains1 (.output 11) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
