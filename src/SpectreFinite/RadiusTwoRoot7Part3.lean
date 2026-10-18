module

public import SpectreFinite.RadiusTwoRoot7Part2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node15Domains0 : Domains 19 State := restrict root7Node13Domains0 15 (6,3)
def root7Node15Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(5,1)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1)]
  | _ => [(0,2)]
theorem root7Node15Step1_checked :
    checkReplacement table14 root7Node15Domains0 root7Node15Domains1 = true := by decide
theorem root7Node15Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node15Domains1 (.output 6) = true := by decide
def root7Node16Domains0 : Domains 19 State := restrict root7Node12Domains4 6 (8,1)
def root7Node16Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(8,1)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node16Step1_checked :
    checkReplacement table10 root7Node16Domains0 root7Node16Domains1 = true := by decide
def root7Node16Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(8,1)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1)]
  | _ => [(0,2)]
theorem root7Node16Step2_checked :
    checkReplacement table14 root7Node16Domains1 root7Node16Domains2 = true := by decide
theorem root7Node16Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node16Domains2 (.output 7) = true := by decide
def root7Node17Domains0 : Domains 19 State := restrict root7Node11Domains1 3 (8,1)
def root7Node17Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(5,2),(5,5),(8,5)]
  | 12 => [(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node17Step1_checked :
    checkReplacement table7 root7Node17Domains0 root7Node17Domains1 = true := by decide
def root7Node17Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(5,2),(5,5),(8,5)]
  | 12 => [(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node17Step2_checked :
    checkReplacement table12 root7Node17Domains1 root7Node17Domains2 = true := by decide
def root7Node18Domains0 : Domains 19 State := restrict root7Node17Domains2 8 (5,5)
def root7Node18Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(5,2),(5,5),(8,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node18Step1_checked :
    checkReplacement table13 root7Node18Domains0 root7Node18Domains1 = true := by decide
def root7Node18Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(5,2),(5,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3),(6,0)]
theorem root7Node18Step2_checked :
    checkReplacement table15 root7Node18Domains1 root7Node18Domains2 = true := by decide
def root7Node19Domains0 : Domains 19 State := restrict root7Node18Domains2 10 (7,3)
def root7Node19Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3),(6,0)]
theorem root7Node19Step1_checked :
    checkReplacement table10 root7Node19Domains0 root7Node19Domains1 = true := by decide
def root7Node19Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3)]
theorem root7Node19Step2_checked :
    checkReplacement table14 root7Node19Domains1 root7Node19Domains2 = true := by decide
theorem root7Node19Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node19Domains2 (.output 8) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
