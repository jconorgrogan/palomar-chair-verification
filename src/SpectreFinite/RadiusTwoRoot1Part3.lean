module

public import SpectreFinite.RadiusTwoRoot1Part2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root1Node8Domains0 : Domains 19 State := restrict root1Node6Domains5 2 (8,2)
theorem root1Node8Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node8Domains0 (.output 4) = true := by decide
def root1Node9Domains0 : Domains 19 State := restrict root1Node5Domains4 3 (5,1)
def root1Node9Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4),(8,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(6,1),(7,1)]
  | 17 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node9Step1_checked :
    checkReplacement table7 root1Node9Domains0 root1Node9Domains1 = true := by decide
def root1Node9Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4),(8,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(7,1)]
  | 17 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node9Step2_checked :
    checkReplacement table12 root1Node9Domains1 root1Node9Domains2 = true := by decide
def root1Node10Domains0 : Domains 19 State := restrict root1Node9Domains2 6 (7,4)
def root1Node10Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(5,0)]
  | 15 => [(3,2),(4,5)]
  | 16 => [(0,4),(1,1),(7,1)]
  | 17 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node10Step1_checked :
    checkReplacement table10 root1Node10Domains0 root1Node10Domains1 = true := by decide
def root1Node10Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(8,2)]
  | 14 => [(0,0),(5,0)]
  | 15 => [(3,2),(4,5)]
  | 16 => [(0,4),(7,1)]
  | 17 => [(1,5),(5,4)]
  | _ => [(0,0),(6,1)]
theorem root1Node10Step2_checked :
    checkReplacement table17 root1Node10Domains1 root1Node10Domains2 = true := by decide
def root1Node10Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,5),(1,3),(6,3)]
  | 13 => [(4,4),(8,2)]
  | 14 => [(0,0),(5,0)]
  | 15 => [(3,2),(4,5)]
  | 16 => [(0,4),(7,1)]
  | 17 => [(1,5),(5,4)]
  | _ => [(0,0),(6,1)]
theorem root1Node10Step3_checked :
    checkReplacement table2 root1Node10Domains2 root1Node10Domains3 = true := by decide
def root1Node10Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,5),(1,3)]
  | 13 => [(4,4),(8,2)]
  | 14 => [(0,0),(5,0)]
  | 15 => [(3,2),(4,5)]
  | 16 => [(0,4),(7,1)]
  | 17 => [(1,5),(5,4)]
  | _ => [(0,0),(6,1)]
theorem root1Node10Step4_checked :
    checkReplacement table8 root1Node10Domains3 root1Node10Domains4 = true := by decide
def root1Node11Domains0 : Domains 19 State := restrict root1Node10Domains4 7 (5,3)
def root1Node12Domains0 : Domains 19 State := restrict root1Node11Domains0 8 (5,5)
def root1Node12Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(3,2),(4,5)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(0,0),(6,1)]
theorem root1Node12Step1_checked :
    checkReplacement table13 root1Node12Domains0 root1Node12Domains1 = true := by decide
def root1Node12Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1)]
  | 11 => [(0,2)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(3,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root1Node12Step2_checked :
    checkReplacement table15 root1Node12Domains1 root1Node12Domains2 = true := by decide
theorem root1Node12Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node12Domains2 (.output 5) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
