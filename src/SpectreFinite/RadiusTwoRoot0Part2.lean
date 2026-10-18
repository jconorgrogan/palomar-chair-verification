module

public import SpectreFinite.RadiusTwoRoot0Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node5Domains0 : Domains 19 State := restrict root0Node0Domains5 5 (4,5)
def root0Node5Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(0,2),(1,0),(1,4),(1,5),(6,0),(6,5)]
  | 1 => [(1,1),(3,1),(6,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(3,5),(5,2),(5,5),(8,2)]
  | 4 => [(3,0),(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0),(7,0)]
  | 7 => [(0,4),(0,5),(1,2),(6,2)]
  | 8 => [(4,4),(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(3,3),(4,0),(7,4)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(0,1),(4,1),(5,1),(8,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(3,0),(7,0)]
  | _ => [(4,5),(7,3),(8,3)]
theorem root0Node5Step1_checked :
    checkReplacement table5 root0Node5Domains0 root0Node5Domains1 = true := by decide
def root0Node5Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0)]
  | 1 => [(1,1),(3,1),(6,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(5,2),(5,5),(8,2)]
  | 4 => [(3,0),(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0),(7,0)]
  | 7 => [(0,4),(0,5),(1,2),(6,2)]
  | 8 => [(4,4),(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(3,3),(4,0),(7,4)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(0,1),(4,1),(5,1),(8,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(3,0),(7,0)]
  | _ => [(4,5),(7,3),(8,3)]
theorem root0Node5Step2_checked :
    checkReplacement table0 root0Node5Domains1 root0Node5Domains2 = true := by decide
def root0Node5Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0)]
  | 1 => [(1,1),(3,1),(6,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(5,2),(5,5),(8,2)]
  | 4 => [(3,0),(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0),(7,0)]
  | 7 => [(0,4),(0,5),(1,2),(6,2)]
  | 8 => [(4,4),(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(3,3),(4,0),(7,4)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(5,1),(8,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node5Step3_checked :
    checkReplacement table14 root0Node5Domains2 root0Node5Domains3 = true := by decide
def root0Node5Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0)]
  | 1 => [(1,1),(3,1),(6,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(5,2),(5,5),(8,2)]
  | 4 => [(3,0),(5,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0),(7,0)]
  | 7 => [(0,4),(0,5),(1,2),(6,2)]
  | 8 => [(4,4),(5,4),(8,4)]
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
theorem root0Node5Step4_checked :
    checkReplacement table6 root0Node5Domains3 root0Node5Domains4 = true := by decide
def root0Node6Domains0 : Domains 19 State := restrict root0Node5Domains4 4 (3,0)
def root0Node6Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(1,1),(3,1),(6,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0),(7,0)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
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
theorem root0Node6Step1_checked :
    checkReplacement table3 root0Node6Domains0 root0Node6Domains1 = true := by decide
def root0Node6Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(0,1)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
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
theorem root0Node6Step2_checked :
    checkReplacement table5 root0Node6Domains1 root0Node6Domains2 = true := by decide
def root0Node6Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(0,1)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0),(7,4)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(5,1),(8,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node6Step3_checked :
    checkReplacement table13 root0Node6Domains2 root0Node6Domains3 = true := by decide
def root0Node6Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(0,1)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node6Step4_checked :
    checkReplacement table10 root0Node6Domains3 root0Node6Domains4 = true := by decide
def root0Node6Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(0,1)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
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
theorem root0Node6Step5_checked :
    checkReplacement table14 root0Node6Domains4 root0Node6Domains5 = true := by decide
theorem root0Node6Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node6Domains5 (.output 3) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
