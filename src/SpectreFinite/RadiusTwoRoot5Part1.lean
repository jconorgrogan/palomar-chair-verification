module

public import SpectreFinite.RadiusTwoRoot5Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root5Node6Domains0 : Domains 19 State := restrict root5Node4Domains0 12 (6,2)
def root5Node6Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(2,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(0,1)]
  | 7 => [(3,3)]
  | 8 => [(5,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node6Step1_checked :
    checkReplacement table12 root5Node6Domains0 root5Node6Domains1 = true := by decide
theorem root5Node6Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node6Domains1 (.output 2) = true := by decide
def root5Node7Domains0 : Domains 19 State := restrict root5Node3Domains1 7 (7,3)
def root5Node8Domains0 : Domains 19 State := restrict root5Node7Domains0 12 (1,2)
def root5Node8Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(2,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(0,1)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
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
theorem root5Node8Step1_checked :
    checkReplacement table12 root5Node8Domains0 root5Node8Domains1 = true := by decide
theorem root5Node8Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node8Domains1 (.output 3) = true := by decide
def root5Node9Domains0 : Domains 19 State := restrict root5Node7Domains0 12 (6,2)
def root5Node9Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(2,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(0,1)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node9Step1_checked :
    checkReplacement table12 root5Node9Domains0 root5Node9Domains1 = true := by decide
theorem root5Node9Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node9Domains1 (.output 4) = true := by decide
def root5Node10Domains0 : Domains 19 State := restrict root5Node0Domains4 8 (8,2)
def root5Node10Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(2,0),(2,2),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 3 => [(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(3,1),(7,1)]
  | 6 => [(0,1),(1,5),(6,5)]
  | 7 => [(1,3),(3,3),(7,3)]
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
theorem root5Node10Step1_checked :
    checkReplacement table4 root5Node10Domains0 root5Node10Domains1 = true := by decide
def root5Node10Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 3 => [(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(3,1),(7,1)]
  | 6 => [(0,1),(1,5),(6,5)]
  | 7 => [(1,3),(3,3),(7,3)]
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
theorem root5Node10Step2_checked :
    checkReplacement table1 root5Node10Domains1 root5Node10Domains2 = true := by decide
def root5Node10Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 3 => [(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
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
theorem root5Node10Step3_checked :
    checkReplacement table3 root5Node10Domains2 root5Node10Domains3 = true := by decide
def root5Node11Domains0 : Domains 19 State := restrict root5Node10Domains3 0 (0,1)
def root5Node11Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(4,0),(7,4),(8,4)]
  | 3 => [(7,5),(8,5)]
  | 4 => [(1,0)]
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
theorem root5Node11Step1_checked :
    checkReplacement table1 root5Node11Domains0 root5Node11Domains1 = true := by decide
def root5Node11Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(4,0),(7,4),(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
  | 5 => [(3,1),(7,1)]
  | 6 => [(0,1),(1,5),(6,5)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0),(7,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3),(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node11Step2_checked :
    checkReplacement table8 root5Node11Domains1 root5Node11Domains2 = true := by decide
def root5Node11Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(4,0),(7,4),(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
  | 5 => [(3,1),(7,1)]
  | 6 => [(0,1),(1,5),(6,5)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0),(7,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node11Step3_checked :
    checkReplacement table12 root5Node11Domains2 root5Node11Domains3 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
