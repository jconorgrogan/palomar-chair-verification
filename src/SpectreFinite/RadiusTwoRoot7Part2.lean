module

public import SpectreFinite.RadiusTwoRoot7Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node9Domains0 : Domains 19 State := restrict root7Node7Domains0 15 (6,3)
def root7Node9Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
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
theorem root7Node9Step1_checked :
    checkReplacement table14 root7Node9Domains0 root7Node9Domains1 = true := by decide
theorem root7Node9Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node9Domains1 (.output 3) = true := by decide
def root7Node10Domains0 : Domains 19 State := restrict root7Node6Domains0 6 (8,1)
def root7Node10Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
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
theorem root7Node10Step1_checked :
    checkReplacement table10 root7Node10Domains0 root7Node10Domains1 = true := by decide
def root7Node10Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
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
theorem root7Node10Step2_checked :
    checkReplacement table14 root7Node10Domains1 root7Node10Domains2 = true := by decide
theorem root7Node10Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node10Domains2 (.output 4) = true := by decide
def root7Node11Domains0 : Domains 19 State := restrict root7Node1Domains3 0 (8,4)
def root7Node11Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,0),(5,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(5,2),(5,5),(8,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node11Step1_checked :
    checkReplacement table1 root7Node11Domains0 root7Node11Domains1 = true := by decide
def root7Node12Domains0 : Domains 19 State := restrict root7Node11Domains1 3 (7,1)
def root7Node12Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(5,2),(5,5),(8,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node12Step1_checked :
    checkReplacement table8 root7Node12Domains0 root7Node12Domains1 = true := by decide
def root7Node12Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(5,2),(5,5),(8,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node12Step2_checked :
    checkReplacement table14 root7Node12Domains1 root7Node12Domains2 = true := by decide
def root7Node12Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(5,1),(8,1)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node12Step3_checked :
    checkReplacement table10 root7Node12Domains2 root7Node12Domains3 = true := by decide
def root7Node12Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(5,1),(8,1)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3),(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node12Step4_checked :
    checkReplacement table12 root7Node12Domains3 root7Node12Domains4 = true := by decide
def root7Node13Domains0 : Domains 19 State := restrict root7Node12Domains4 6 (5,1)
def root7Node14Domains0 : Domains 19 State := restrict root7Node13Domains0 15 (1,3)
def root7Node14Domains1 (v : Fin 19) : List State :=
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
  | 15 => [(1,3)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | _ => [(6,5)]
theorem root7Node14Step1_checked :
    checkReplacement table14 root7Node14Domains0 root7Node14Domains1 = true := by decide
theorem root7Node14Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node14Domains1 (.output 5) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
