module

public import SpectreFinite.RadiusTwoRoot1Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root1Node5Domains0 : Domains 19 State := restrict root1Node0Domains4 0 (4,0)
def root1Node5Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(0,2),(4,2),(5,2),(8,2)]
  | 3 => [(3,1),(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(4,0),(7,4),(8,4)]
  | 7 => [(3,0),(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(6,1),(7,1)]
  | 17 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node5Step1_checked :
    checkReplacement table0 root1Node5Domains0 root1Node5Domains1 = true := by decide
def root1Node5Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(3,1),(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4),(8,4)]
  | 7 => [(3,0),(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(6,1),(7,1)]
  | 17 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node5Step2_checked :
    checkReplacement table5 root1Node5Domains1 root1Node5Domains2 = true := by decide
def root1Node5Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(3,1),(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4),(8,4)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(6,1),(7,1)]
  | 17 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node5Step3_checked :
    checkReplacement table3 root1Node5Domains2 root1Node5Domains3 = true := by decide
def root1Node5Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(3,1),(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4),(8,4)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(6,1),(7,1)]
  | 17 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node5Step4_checked :
    checkReplacement table6 root1Node5Domains3 root1Node5Domains4 = true := by decide
def root1Node6Domains0 : Domains 19 State := restrict root1Node5Domains4 3 (3,1)
def root1Node6Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(3,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4),(8,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(6,1),(7,1)]
  | 17 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node6Step1_checked :
    checkReplacement table8 root1Node6Domains0 root1Node6Domains1 = true := by decide
def root1Node6Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(3,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4),(8,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4),(1,1),(6,1),(7,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root1Node6Step2_checked :
    checkReplacement table14 root1Node6Domains1 root1Node6Domains2 = true := by decide
def root1Node6Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(3,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4),(1,1),(6,1),(7,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root1Node6Step3_checked :
    checkReplacement table10 root1Node6Domains2 root1Node6Domains3 = true := by decide
def root1Node6Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(3,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root1Node6Step4_checked :
    checkReplacement table12 root1Node6Domains3 root1Node6Domains4 = true := by decide
def root1Node6Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(3,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root1Node6Step5_checked :
    checkReplacement table2 root1Node6Domains4 root1Node6Domains5 = true := by decide
def root1Node7Domains0 : Domains 19 State := restrict root1Node6Domains5 2 (5,2)
theorem root1Node7Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node7Domains0 (.output 3) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
