module

public import SpectreFinite.RadiusTwoRoot7Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node2Domains0 : Domains 19 State := restrict root7Node1Domains3 0 (4,4)
def root7Node2Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2),(7,2)]
  | 3 => [(7,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
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
theorem root7Node2Step1_checked :
    checkReplacement table3 root7Node2Domains0 root7Node2Domains1 = true := by decide
def root7Node2Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2),(7,2)]
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
  | 14 => [(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node2Step2_checked :
    checkReplacement table13 root7Node2Domains1 root7Node2Domains2 = true := by decide
def root7Node2Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2),(7,2)]
  | 3 => [(7,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
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
theorem root7Node2Step3_checked :
    checkReplacement table15 root7Node2Domains2 root7Node2Domains3 = true := by decide
def root7Node2Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2),(7,2)]
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
theorem root7Node2Step4_checked :
    checkReplacement table5 root7Node2Domains3 root7Node2Domains4 = true := by decide
def root7Node3Domains0 : Domains 19 State := restrict root7Node2Domains4 2 (3,2)
def root7Node3Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2)]
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
  | 15 => [(1,3),(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node3Step1_checked :
    checkReplacement table2 root7Node3Domains0 root7Node3Domains1 = true := by decide
def root7Node4Domains0 : Domains 19 State := restrict root7Node3Domains1 15 (1,3)
def root7Node4Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2)]
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
theorem root7Node4Step1_checked :
    checkReplacement table14 root7Node4Domains0 root7Node4Domains1 = true := by decide
theorem root7Node4Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node4Domains1 (.output 0) = true := by decide
def root7Node5Domains0 : Domains 19 State := restrict root7Node3Domains1 15 (6,3)
def root7Node5Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2)]
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
theorem root7Node5Step1_checked :
    checkReplacement table14 root7Node5Domains0 root7Node5Domains1 = true := by decide
theorem root7Node5Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node5Domains1 (.output 1) = true := by decide
def root7Node6Domains0 : Domains 19 State := restrict root7Node2Domains4 2 (7,2)
def root7Node7Domains0 : Domains 19 State := restrict root7Node6Domains0 6 (5,1)
def root7Node8Domains0 : Domains 19 State := restrict root7Node7Domains0 15 (1,3)
def root7Node8Domains1 (v : Fin 19) : List State :=
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
  | 15 => [(1,3)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | _ => [(6,5)]
theorem root7Node8Step1_checked :
    checkReplacement table14 root7Node8Domains0 root7Node8Domains1 = true := by decide
theorem root7Node8Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node8Domains1 (.output 2) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
