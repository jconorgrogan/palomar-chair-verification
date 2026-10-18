module

public import SpectreFinite.RadiusTwoRoot0Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node2Domains0 : Domains 19 State := restrict root0Node1Domains4 0 (0,1)
def root0Node2Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(2,4),(7,4)]
  | 3 => [(5,5)]
  | 4 => [(1,0)]
  | 5 => [(2,1)]
  | 6 => [(0,2)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(4,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node2Step1_checked :
    checkReplacement table0 root0Node2Domains0 root0Node2Domains1 = true := by decide
def root0Node2Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(7,4)]
  | 3 => [(5,5)]
  | 4 => [(1,0)]
  | 5 => [(2,1)]
  | 6 => [(0,2)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(4,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node2Step2_checked :
    checkReplacement table1 root0Node2Domains1 root0Node2Domains2 = true := by decide
theorem root0Node2Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node2Domains2 (.output 0) = true := by decide
def root0Node3Domains0 : Domains 19 State := restrict root0Node1Domains4 0 (1,4)
def root0Node3Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,4),(7,4)]
  | 3 => [(3,5)]
  | 4 => [(6,0)]
  | 5 => [(2,1)]
  | 6 => [(0,2)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(4,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node3Step1_checked :
    checkReplacement table0 root0Node3Domains0 root0Node3Domains1 = true := by decide
def root0Node3Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,4)]
  | 3 => [(3,5)]
  | 4 => [(6,0)]
  | 5 => [(2,1)]
  | 6 => [(0,2)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(4,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node3Step2_checked :
    checkReplacement table1 root0Node3Domains1 root0Node3Domains2 = true := by decide
theorem root0Node3Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node3Domains2 (.output 1) = true := by decide
def root0Node4Domains0 : Domains 19 State := restrict root0Node0Domains5 5 (2,5)
def root0Node4Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(1,4),(6,4)]
  | 3 => [(3,5),(5,2),(5,5),(8,2)]
  | 4 => [(3,0)]
  | 5 => [(2,5)]
  | 6 => [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 7 => [(0,4),(0,5),(1,2),(6,2)]
  | 8 => [(4,4),(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(2,2),(3,2),(7,2)]
  | 11 => [(3,3),(4,0),(7,4)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(0,1),(4,1),(5,1),(8,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(3,0),(7,0)]
  | _ => [(4,5),(7,3),(8,3)]
theorem root0Node4Step1_checked :
    checkReplacement table1 root0Node4Domains0 root0Node4Domains1 = true := by decide
def root0Node4Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(1,4),(6,4)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(2,5)]
  | 6 => [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(2,2),(3,2),(7,2)]
  | 11 => [(3,3),(4,0),(7,4)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(0,1),(4,1),(5,1),(8,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(3,0),(7,0)]
  | _ => [(4,5),(7,3),(8,3)]
theorem root0Node4Step2_checked :
    checkReplacement table8 root0Node4Domains1 root0Node4Domains2 = true := by decide
def root0Node4Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(1,4),(6,4)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(2,5)]
  | 6 => [(0,3),(6,0)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(2,2),(7,2)]
  | 11 => [(3,3),(4,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(0,1),(5,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(3,0),(7,0)]
  | _ => [(4,5),(7,3),(8,3)]
theorem root0Node4Step3_checked :
    checkReplacement table10 root0Node4Domains2 root0Node4Domains3 = true := by decide
def root0Node4Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(1,4),(6,4)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(2,5)]
  | 6 => [(0,3),(6,0)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(2,2),(7,2)]
  | 11 => [(3,3),(4,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(0,1),(5,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(4,5),(7,3),(8,3)]
theorem root0Node4Step4_checked :
    checkReplacement table13 root0Node4Domains3 root0Node4Domains4 = true := by decide
def root0Node4Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(1,4),(6,4)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(2,5)]
  | 6 => [(0,3),(6,0)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(3,3),(4,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(5,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node4Step5_checked :
    checkReplacement table14 root0Node4Domains4 root0Node4Domains5 = true := by decide
def root0Node4Domains6 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(1,4)]
  | 3 => [(5,5)]
  | 4 => [(3,0)]
  | 5 => [(2,5)]
  | 6 => [(6,0)]
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
theorem root0Node4Step6_checked :
    checkReplacement table6 root0Node4Domains5 root0Node4Domains6 = true := by decide
theorem root0Node4Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node4Domains6 (.output 2) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
