module

public import SpectreFinite.RadiusTwoRoot1Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root1Node2Domains0 : Domains 19 State := restrict root1Node0Domains4 0 (2,2)
def root1Node2Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(2,3),(3,3),(7,3)]
  | 2 => [(0,2),(4,2),(5,2),(8,2)]
  | 3 => [(1,1),(6,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(4,0),(7,4),(8,4)]
  | 7 => [(3,0),(5,0)]
  | 8 => [(4,5)]
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
theorem root1Node2Step1_checked :
    checkReplacement table3 root1Node2Domains0 root1Node2Domains1 = true := by decide
def root1Node2Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(2,3),(3,3),(7,3)]
  | 2 => [(0,2),(4,2),(5,2),(8,2)]
  | 3 => [(1,1),(6,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(4,0),(7,4),(8,4)]
  | 7 => [(3,0),(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node2Step2_checked :
    checkReplacement table13 root1Node2Domains1 root1Node2Domains2 = true := by decide
def root1Node2Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(2,3),(3,3),(7,3)]
  | 2 => [(0,2),(4,2),(5,2),(8,2)]
  | 3 => [(1,1),(6,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(4,0),(7,4),(8,4)]
  | 7 => [(3,0),(5,0)]
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
theorem root1Node2Step3_checked :
    checkReplacement table15 root1Node2Domains2 root1Node2Domains3 = true := by decide
def root1Node2Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(1,1),(6,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(4,0),(7,4),(8,4)]
  | 7 => [(3,0),(5,0)]
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
theorem root1Node2Step4_checked :
    checkReplacement table1 root1Node2Domains3 root1Node2Domains4 = true := by decide
def root1Node2Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(1,1),(6,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(3,0),(5,0)]
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
theorem root1Node2Step5_checked :
    checkReplacement table2 root1Node2Domains4 root1Node2Domains5 = true := by decide
def root1Node3Domains0 : Domains 19 State := restrict root1Node2Domains5 3 (1,1)
def root1Node3Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(1,1)]
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
theorem root1Node3Step1_checked :
    checkReplacement table3 root1Node3Domains0 root1Node3Domains1 = true := by decide
theorem root1Node3Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node3Domains1 (.output 1) = true := by decide
def root1Node4Domains0 : Domains 19 State := restrict root1Node2Domains5 3 (6,1)
def root1Node4Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(6,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(3,0)]
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
theorem root1Node4Step1_checked :
    checkReplacement table3 root1Node4Domains0 root1Node4Domains1 = true := by decide
theorem root1Node4Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node4Domains1 (.output 2) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
