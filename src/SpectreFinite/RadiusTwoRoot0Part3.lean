module

public import SpectreFinite.RadiusTwoRoot0Part2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node7Domains0 : Domains 19 State := restrict root0Node5Domains4 4 (5,0)
def root0Node7Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(6,0)]
  | 1 => [(1,1),(3,1),(6,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(5,2),(8,2)]
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
theorem root0Node7Step1_checked :
    checkReplacement table3 root0Node7Domains0 root0Node7Domains1 = true := by decide
def root0Node7Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(6,0)]
  | 1 => [(1,1),(3,1),(7,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(5,2),(8,2)]
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
theorem root0Node7Step2_checked :
    checkReplacement table0 root0Node7Domains1 root0Node7Domains2 = true := by decide
def root0Node8Domains0 : Domains 19 State := restrict root0Node7Domains2 3 (5,2)
def root0Node8Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(0,1),(1,5),(6,5)]
  | 3 => [(5,2)]
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
theorem root0Node8Step1_checked :
    checkReplacement table0 root0Node8Domains0 root0Node8Domains1 = true := by decide
def root0Node8Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(0,1)]
  | 3 => [(5,2)]
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
theorem root0Node8Step2_checked :
    checkReplacement table2 root0Node8Domains1 root0Node8Domains2 = true := by decide
def root0Node8Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(0,1)]
  | 3 => [(5,2)]
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
theorem root0Node8Step3_checked :
    checkReplacement table10 root0Node8Domains2 root0Node8Domains3 = true := by decide
def root0Node8Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(0,1)]
  | 3 => [(5,2)]
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
theorem root0Node8Step4_checked :
    checkReplacement table14 root0Node8Domains3 root0Node8Domains4 = true := by decide
def root0Node8Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(0,1)]
  | 3 => [(5,2)]
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
theorem root0Node8Step5_checked :
    checkReplacement table13 root0Node8Domains4 root0Node8Domains5 = true := by decide
def root0Node8Domains6 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(0,1)]
  | 3 => [(5,2)]
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
theorem root0Node8Step6_checked :
    checkReplacement table3 root0Node8Domains5 root0Node8Domains6 = true := by decide
def root0Node9Domains0 : Domains 19 State := restrict root0Node8Domains6 7 (1,2)
def root0Node9Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(0,1)]
  | 3 => [(5,2)]
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
theorem root0Node9Step1_checked :
    checkReplacement table12 root0Node9Domains0 root0Node9Domains1 = true := by decide
def root0Node10Domains0 : Domains 19 State := restrict root0Node9Domains1 16 (5,5)
theorem root0Node10Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node10Domains0 (.output 4) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
