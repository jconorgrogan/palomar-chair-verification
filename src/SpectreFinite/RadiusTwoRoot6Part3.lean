module

public import SpectreFinite.RadiusTwoRoot6Part2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root6Node15Domains0 : Domains 19 State := restrict root6Node11Domains1 6 (4,4)
def root6Node15Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0)]
theorem root6Node15Step1_checked :
    checkReplacement table6 root6Node15Domains0 root6Node15Domains1 = true := by decide
def root6Node16Domains0 : Domains 19 State := restrict root6Node15Domains1 16 (1,2)
theorem root6Node16Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node16Domains0 (.output 7) = true := by decide
def root6Node17Domains0 : Domains 19 State := restrict root6Node15Domains1 16 (6,2)
theorem root6Node17Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node17Domains0 (.output 8) = true := by decide
def root6Node18Domains0 : Domains 19 State := restrict root6Node2Domains6 1 (8,3)
def root6Node18Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,1),(1,5),(6,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0),(6,4)]
theorem root6Node18Step1_checked :
    checkReplacement table5 root6Node18Domains0 root6Node18Domains1 = true := by decide
def root6Node18Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0),(6,4)]
theorem root6Node18Step2_checked :
    checkReplacement table6 root6Node18Domains1 root6Node18Domains2 = true := by decide
def root6Node19Domains0 : Domains 19 State := restrict root6Node18Domains2 11 (1,5)
def root6Node19Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0)]
theorem root6Node19Step1_checked :
    checkReplacement table15 root6Node19Domains0 root6Node19Domains1 = true := by decide
def root6Node20Domains0 : Domains 19 State := restrict root6Node19Domains1 16 (1,2)
theorem root6Node20Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node20Domains0 (.output 9) = true := by decide
def root6Node21Domains0 : Domains 19 State := restrict root6Node19Domains1 16 (6,2)
theorem root6Node21Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node21Domains0 (.output 10) = true := by decide
def root6Node22Domains0 : Domains 19 State := restrict root6Node18Domains2 11 (7,5)
def root6Node22Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(6,4)]
theorem root6Node22Step1_checked :
    checkReplacement table15 root6Node22Domains0 root6Node22Domains1 = true := by decide
def root6Node22Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | _ => [(6,4)]
theorem root6Node22Step2_checked :
    checkReplacement table13 root6Node22Domains1 root6Node22Domains2 = true := by decide
theorem root6Node22Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node22Domains2 (.output 11) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
