module

public import SpectreFinite.RadiusTwoRoot5Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root5Node0Domains0 : Domains 19 State := domains (5,0)
def root5Node0Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => stateChoices
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => stateChoices
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node0Step1_checked :
    checkReplacement table14 root5Node0Domains0 root5Node0Domains1 = true := by decide
def root5Node0Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => stateChoices
  | 3 => [(4,1),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(3,1),(7,1)]
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(5,2),(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => stateChoices
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node0Step2_checked :
    checkReplacement table4 root5Node0Domains1 root5Node0Domains2 = true := by decide
def root5Node0Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => stateChoices
  | 3 => [(4,1),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(3,1),(7,1)]
  | 6 => stateChoices
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => stateChoices
  | 12 => [(0,4),(1,2),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3),(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node0Step3_checked :
    checkReplacement table12 root5Node0Domains2 root5Node0Domains3 = true := by decide
def root5Node0Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(2,0),(2,2),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 3 => [(4,1),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(3,1),(7,1)]
  | 6 => [(0,1),(1,5),(6,5)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2),(8,2)]
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
theorem root5Node0Step4_checked :
    checkReplacement table6 root5Node0Domains3 root5Node0Domains4 = true := by decide
def root5Node1Domains0 : Domains 19 State := restrict root5Node0Domains4 8 (5,2)
def root5Node1Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(2,0),(2,2),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(0,1),(1,5),(6,5)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2)]
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
theorem root5Node1Step1_checked :
    checkReplacement table4 root5Node1Domains0 root5Node1Domains1 = true := by decide
def root5Node1Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(2,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(0,1)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(0,4),(1,2),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3),(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node1Step2_checked :
    checkReplacement table6 root5Node1Domains1 root5Node1Domains2 = true := by decide
def root5Node2Domains0 : Domains 19 State := restrict root5Node1Domains2 13 (5,4)
def root5Node2Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(2,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(0,1)]
  | 7 => [(1,3)]
  | 8 => [(5,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node2Step1_checked :
    checkReplacement table12 root5Node2Domains0 root5Node2Domains1 = true := by decide
theorem root5Node2Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node2Domains1 (.output 0) = true := by decide
def root5Node3Domains0 : Domains 19 State := restrict root5Node1Domains2 13 (8,4)
def root5Node3Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(2,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(0,1)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(1,2),(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node3Step1_checked :
    checkReplacement table12 root5Node3Domains0 root5Node3Domains1 = true := by decide
def root5Node4Domains0 : Domains 19 State := restrict root5Node3Domains1 7 (3,3)
def root5Node5Domains0 : Domains 19 State := restrict root5Node4Domains0 12 (1,2)
def root5Node5Domains1 (v : Fin 19) : List State :=
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
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node5Step1_checked :
    checkReplacement table12 root5Node5Domains0 root5Node5Domains1 = true := by decide
theorem root5Node5Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node5Domains1 (.output 1) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
