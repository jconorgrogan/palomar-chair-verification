module

public import SpectreFinite.RadiusTwoRoot3Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root3Node0Domains0 : Domains 19 State := domains (3,0)
def root3Node0Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => stateChoices
  | 11 => stateChoices
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => stateChoices
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => stateChoices
theorem root3Node0Step1_checked :
    checkReplacement table13 root3Node0Domains0 root3Node0Domains1 = true := by decide
def root3Node0Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(0,0),(1,3)]
  | 2 => [(2,2),(4,2)]
  | 3 => stateChoices
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => [(0,1),(1,4),(6,4)]
  | 7 => stateChoices
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5),(4,5)]
  | 11 => stateChoices
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => stateChoices
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => stateChoices
theorem root3Node0Step2_checked :
    checkReplacement table5 root3Node0Domains1 root3Node0Domains2 = true := by decide
def root3Node0Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4),(8,4)]
  | 1 => [(0,0),(1,3)]
  | 2 => [(2,2),(4,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => [(0,1),(1,4),(6,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5),(4,5)]
  | 11 => stateChoices
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => stateChoices
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => stateChoices
theorem root3Node0Step3_checked :
    checkReplacement table3 root3Node0Domains2 root3Node0Domains3 = true := by decide
def root3Node0Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4),(8,4)]
  | 1 => [(0,0),(1,3)]
  | 2 => [(2,2),(4,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => [(0,1),(1,4),(6,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5),(4,5)]
  | 11 => [(0,3),(1,0),(6,0),(7,0)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(2,2),(7,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root3Node0Step4_checked :
    checkReplacement table15 root3Node0Domains3 root3Node0Domains4 = true := by decide
def root3Node0Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(0,1),(1,4),(6,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5),(4,5)]
  | 11 => [(0,3),(1,0),(6,0),(7,0)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(2,2),(7,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root3Node0Step5_checked :
    checkReplacement table1 root3Node0Domains4 root3Node0Domains5 = true := by decide
def root3Node0Domains6 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(1,4),(6,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5)]
  | 11 => [(0,3),(6,0)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(2,2),(7,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root3Node0Step6_checked :
    checkReplacement table6 root3Node0Domains5 root3Node0Domains6 = true := by decide
def root3Node1Domains0 : Domains 19 State := restrict root3Node0Domains6 6 (1,4)
def root3Node1Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(1,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5)]
  | 11 => [(6,0)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root3Node1Step1_checked :
    checkReplacement table10 root3Node1Domains0 root3Node1Domains1 = true := by decide
def root3Node2Domains0 : Domains 19 State := restrict root3Node1Domains1 7 (5,3)
theorem root3Node2Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node2Domains0 (.output 0) = true := by decide
def root3Node3Domains0 : Domains 19 State := restrict root3Node1Domains1 7 (8,3)
theorem root3Node3Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node3Domains0 (.output 1) = true := by decide
def root3Node4Domains0 : Domains 19 State := restrict root3Node0Domains6 6 (6,4)
def root3Node4Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(6,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5)]
  | 11 => [(0,3)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(2,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root3Node4Step1_checked :
    checkReplacement table10 root3Node4Domains0 root3Node4Domains1 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
