module

public import SpectreFinite.RadiusTwoRoot0Part3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node11Domains0 : Domains 19 State := restrict root0Node9Domains1 16 (8,5)
theorem root0Node11Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node11Domains0 (.output 5) = true := by decide
def root0Node12Domains0 : Domains 19 State := restrict root0Node8Domains6 7 (6,2)
def root0Node12Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(0,1)]
  | 3 => [(5,2)]
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
theorem root0Node12Step1_checked :
    checkReplacement table12 root0Node12Domains0 root0Node12Domains1 = true := by decide
theorem root0Node12Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node12Domains1 (.output 6) = true := by decide
def root0Node13Domains0 : Domains 19 State := restrict root0Node7Domains2 3 (8,2)
def root0Node13Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,0),(6,0)]
  | 1 => [(3,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0),(7,0)]
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
theorem root0Node13Step1_checked :
    checkReplacement table0 root0Node13Domains0 root0Node13Domains1 = true := by decide
def root0Node14Domains0 : Domains 19 State := restrict root0Node13Domains1 0 (1,0)
def root0Node14Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(3,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0),(7,0)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
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
theorem root0Node14Step1_checked :
    checkReplacement table3 root0Node14Domains0 root0Node14Domains1 = true := by decide
def root0Node14Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(3,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0),(7,0)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0),(7,4)]
  | 12 => [(4,3)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(5,1),(8,1)]
  | 16 => [(0,5)]
  | 17 => [(2,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node14Step2_checked :
    checkReplacement table13 root0Node14Domains1 root0Node14Domains2 = true := by decide
def root0Node14Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(3,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0),(7,0)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0),(7,4)]
  | 12 => [(4,3)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1)]
  | 16 => [(0,5)]
  | 17 => [(2,0)]
  | _ => [(7,3)]
theorem root0Node14Step3_checked :
    checkReplacement table14 root0Node14Domains2 root0Node14Domains3 = true := by decide
def root0Node14Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(3,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
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
theorem root0Node14Step4_checked :
    checkReplacement table10 root0Node14Domains3 root0Node14Domains4 = true := by decide
def root0Node14Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5),(6,5)]
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
theorem root0Node14Step5_checked :
    checkReplacement table2 root0Node14Domains4 root0Node14Domains5 = true := by decide
def root0Node15Domains0 : Domains 19 State := restrict root0Node14Domains5 2 (1,5)
theorem root0Node15Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node15Domains0 (.output 7) = true := by decide
def root0Node16Domains0 : Domains 19 State := restrict root0Node14Domains5 2 (6,5)
theorem root0Node16Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node16Domains0 (.output 8) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
