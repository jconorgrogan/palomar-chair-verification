module

public import SpectreFinite.RadiusTwoRoot8Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root8Node0Domains0 : Domains 19 State := domains (8,0)
def root8Node0Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => stateChoices
  | 11 => stateChoices
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => stateChoices
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => stateChoices
theorem root8Node0Step1_checked :
    checkReplacement table13 root8Node0Domains0 root8Node0Domains1 = true := by decide
def root8Node0Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(3,2),(4,4),(7,2),(8,4)]
  | 3 => stateChoices
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(7,1)]
  | 6 => [(4,1),(5,1),(7,5),(8,1)]
  | 7 => stateChoices
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => stateChoices
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => stateChoices
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => stateChoices
theorem root8Node0Step2_checked :
    checkReplacement table5 root8Node0Domains1 root8Node0Domains2 = true := by decide
def root8Node0Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(3,2),(4,4),(7,2),(8,4)]
  | 3 => stateChoices
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(7,1)]
  | 6 => [(4,1),(5,1),(7,5),(8,1)]
  | 7 => stateChoices
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(4,2),(5,2),(5,5),(8,2)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3),(6,0)]
theorem root8Node0Step3_checked :
    checkReplacement table15 root8Node0Domains2 root8Node0Domains3 = true := by decide
def root8Node0Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(3,2),(4,4),(7,2),(8,4)]
  | 3 => [(4,1),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(7,1)]
  | 6 => [(4,1),(5,1),(7,5),(8,1)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(4,2),(5,2),(5,5),(8,2)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3),(6,0)]
theorem root8Node0Step4_checked :
    checkReplacement table3 root8Node0Domains3 root8Node0Domains4 = true := by decide
def root8Node0Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(4,1),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(7,1)]
  | 6 => [(4,1),(5,1),(7,5),(8,1)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(4,2),(5,2),(5,5),(8,2)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3),(6,0)]
theorem root8Node0Step5_checked :
    checkReplacement table1 root8Node0Domains4 root8Node0Domains5 = true := by decide
def root8Node1Domains0 : Domains 19 State := restrict root8Node0Domains5 5 (1,1)
def root8Node1Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1),(5,1),(7,5),(8,1)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(4,2),(5,2),(5,5),(8,2)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3),(6,0)]
theorem root8Node1Step1_checked :
    checkReplacement table4 root8Node1Domains0 root8Node1Domains1 = true := by decide
def root8Node1Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(5,2),(5,5)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3),(6,0)]
theorem root8Node1Step2_checked :
    checkReplacement table6 root8Node1Domains1 root8Node1Domains2 = true := by decide
def root8Node2Domains0 : Domains 19 State := restrict root8Node1Domains2 10 (7,3)
def root8Node2Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3),(6,0)]
theorem root8Node2Step1_checked :
    checkReplacement table10 root8Node2Domains0 root8Node2Domains1 = true := by decide
def root8Node2Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3)]
theorem root8Node2Step2_checked :
    checkReplacement table14 root8Node2Domains1 root8Node2Domains2 = true := by decide
def root8Node3Domains0 : Domains 19 State := restrict root8Node2Domains2 12 (0,4)
def root8Node3Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(1,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(4,3)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3)]
theorem root8Node3Step1_checked :
    checkReplacement table12 root8Node3Domains0 root8Node3Domains1 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
