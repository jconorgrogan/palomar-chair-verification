module

public import SpectreFinite.RadiusTwoRoot5Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root5Node12Domains0 : Domains 19 State := restrict root5Node11Domains3 5 (3,1)
def root5Node12Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(4,0)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
  | 5 => [(3,1)]
  | 6 => [(0,1)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node12Step1_checked :
    checkReplacement table6 root5Node12Domains0 root5Node12Domains1 = true := by decide
theorem root5Node12Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node12Domains1 (.output 5) = true := by decide
def root5Node13Domains0 : Domains 19 State := restrict root5Node11Domains3 5 (7,1)
def root5Node13Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(7,4),(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
  | 5 => [(7,1)]
  | 6 => [(1,5),(6,5)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node13Step1_checked :
    checkReplacement table6 root5Node13Domains0 root5Node13Domains1 = true := by decide
def root5Node14Domains0 : Domains 19 State := restrict root5Node13Domains1 2 (7,4)
def root5Node14Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(7,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
  | 5 => [(7,1)]
  | 6 => [(6,5)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node14Step1_checked :
    checkReplacement table2 root5Node14Domains0 root5Node14Domains1 = true := by decide
theorem root5Node14Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node14Domains1 (.output 6) = true := by decide
def root5Node15Domains0 : Domains 19 State := restrict root5Node13Domains1 2 (8,4)
def root5Node15Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
  | 5 => [(7,1)]
  | 6 => [(1,5)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node15Step1_checked :
    checkReplacement table2 root5Node15Domains0 root5Node15Domains1 = true := by decide
theorem root5Node15Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node15Domains1 (.output 7) = true := by decide
def root5Node16Domains0 : Domains 19 State := restrict root5Node10Domains3 0 (1,4)
def root5Node16Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,0),(2,4),(4,4)]
  | 3 => [(7,5),(8,5)]
  | 4 => [(6,0)]
  | 5 => [(3,1),(7,1)]
  | 6 => [(0,1),(1,5),(6,5)]
  | 7 => [(1,3),(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0),(7,0)]
  | 12 => [(0,4),(1,2),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3),(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node16Step1_checked :
    checkReplacement table1 root5Node16Domains0 root5Node16Domains1 = true := by decide
def root5Node16Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,0),(2,4),(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(3,1),(7,1)]
  | 6 => [(0,1),(1,5),(6,5)]
  | 7 => [(1,3),(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0),(7,0)]
  | 12 => [(0,4),(1,2),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3),(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node16Step2_checked :
    checkReplacement table0 root5Node16Domains1 root5Node16Domains2 = true := by decide
def root5Node17Domains0 : Domains 19 State := restrict root5Node16Domains2 5 (3,1)
def root5Node17Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,0)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(3,1)]
  | 6 => [(0,1)]
  | 7 => [(1,3),(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(0,4),(1,2),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3),(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node17Step1_checked :
    checkReplacement table6 root5Node17Domains0 root5Node17Domains1 = true := by decide
def root5Node18Domains0 : Domains 19 State := restrict root5Node17Domains1 7 (1,3)
def root5Node18Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,0)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(3,1)]
  | 6 => [(0,1)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node18Step1_checked :
    checkReplacement table12 root5Node18Domains0 root5Node18Domains1 = true := by decide
theorem root5Node18Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node18Domains1 (.output 8) = true := by decide
def root5Node19Domains0 : Domains 19 State := restrict root5Node17Domains1 7 (7,3)
def root5Node19Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,0)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(3,1)]
  | 6 => [(0,1)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(1,2),(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node19Step1_checked :
    checkReplacement table12 root5Node19Domains0 root5Node19Domains1 = true := by decide
def root5Node20Domains0 : Domains 19 State := restrict root5Node19Domains1 12 (1,2)
def root5Node20Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,0)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(3,1)]
  | 6 => [(0,1)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node20Step1_checked :
    checkReplacement table12 root5Node20Domains0 root5Node20Domains1 = true := by decide
theorem root5Node20Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node20Domains1 (.output 9) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
