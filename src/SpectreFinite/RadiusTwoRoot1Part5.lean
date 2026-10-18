module

public import SpectreFinite.RadiusTwoRoot1Part4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root1Node17Domains0 : Domains 19 State := restrict root1Node9Domains2 6 (8,4)
def root1Node17Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(7,1)]
  | 17 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node17Step1_checked :
    checkReplacement table10 root1Node17Domains0 root1Node17Domains1 = true := by decide
def root1Node17Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node17Step2_checked :
    checkReplacement table13 root1Node17Domains1 root1Node17Domains2 = true := by decide
def root1Node17Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node17Step3_checked :
    checkReplacement table2 root1Node17Domains2 root1Node17Domains3 = true := by decide
def root1Node17Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,4)]
theorem root1Node17Step4_checked :
    checkReplacement table14 root1Node17Domains3 root1Node17Domains4 = true := by decide
def root1Node18Domains0 : Domains 19 State := restrict root1Node17Domains4 2 (5,2)
def root1Node19Domains0 : Domains 19 State := restrict root1Node18Domains0 7 (5,3)
def root1Node20Domains0 : Domains 19 State := restrict root1Node19Domains0 11 (1,5)
def root1Node20Domains1 (v : Fin 19) : List State :=
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
  | 11 => [(1,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,0)]
theorem root1Node20Step1_checked :
    checkReplacement table15 root1Node20Domains0 root1Node20Domains1 = true := by decide
def root1Node20Domains2 (v : Fin 19) : List State :=
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
  | 11 => [(1,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,0)]
theorem root1Node20Step2_checked :
    checkReplacement table13 root1Node20Domains1 root1Node20Domains2 = true := by decide
theorem root1Node20Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node20Domains2 (.output 9) = true := by decide
def root1Node21Domains0 : Domains 19 State := restrict root1Node19Domains0 11 (7,5)
def root1Node21Domains1 (v : Fin 19) : List State :=
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
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,1),(6,4)]
theorem root1Node21Step1_checked :
    checkReplacement table15 root1Node21Domains0 root1Node21Domains1 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
