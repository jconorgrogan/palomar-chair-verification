module

public import SpectreFinite.RadiusTwoRoot4Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root4Node0Domains0 : Domains 19 State := domains (4,0)
def root4Node0Domains1 (v : Fin 19) : List State :=
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
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => stateChoices
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node0Step1_checked :
    checkReplacement table14 root4Node0Domains0 root4Node0Domains1 = true := by decide
def root4Node0Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(2,4),(3,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => stateChoices
  | 3 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(7,1)]
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(1,2),(3,2),(6,2),(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => stateChoices
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node0Step2_checked :
    checkReplacement table4 root4Node0Domains1 root4Node0Domains2 = true := by decide
def root4Node0Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(2,4),(3,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(7,1)]
  | 6 => [(4,1),(7,5)]
  | 7 => stateChoices
  | 8 => [(1,2),(3,2),(6,2),(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(5,2),(8,2)]
  | 12 => stateChoices
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => stateChoices
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node0Step3_checked :
    checkReplacement table6 root4Node0Domains2 root4Node0Domains3 = true := by decide
def root4Node0Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(2,4),(3,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(7,1)]
  | 6 => [(4,1),(7,5)]
  | 7 => [(0,0),(0,1),(6,3),(6,4)]
  | 8 => [(1,2),(3,2),(6,2),(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(5,2),(8,2)]
  | 12 => [(0,3),(1,0),(1,1),(6,1)]
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node0Step4_checked :
    checkReplacement table12 root4Node0Domains3 root4Node0Domains4 = true := by decide
def root4Node0Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 4 => [(0,2),(1,0),(6,0)]
  | 5 => [(1,1),(7,1)]
  | 6 => [(4,1),(7,5)]
  | 7 => [(0,0),(0,1),(6,3),(6,4)]
  | 8 => [(1,2),(3,2),(6,2),(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(5,2),(8,2)]
  | 12 => [(0,3),(1,0),(1,1),(6,1)]
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node0Step5_checked :
    checkReplacement table1 root4Node0Domains4 root4Node0Domains5 = true := by decide
def root4Node1Domains0 : Domains 19 State := restrict root4Node0Domains5 5 (1,1)
def root4Node1Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4),(7,4)]
  | 1 => [(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(2,1),(2,3),(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1),(7,5)]
  | 7 => [(0,0),(0,1),(6,3),(6,4)]
  | 8 => [(1,2),(3,2),(6,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(5,2),(8,2)]
  | 12 => [(0,3),(1,0),(1,1),(6,1)]
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node1Step1_checked :
    checkReplacement table4 root4Node1Domains0 root4Node1Domains1 = true := by decide
def root4Node1Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4),(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,1),(2,3),(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(0,0),(0,1),(6,3),(6,4)]
  | 8 => [(1,2),(3,2),(6,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,3),(1,0),(1,1),(6,1)]
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node1Step2_checked :
    checkReplacement table6 root4Node1Domains1 root4Node1Domains2 = true := by decide
def root4Node2Domains0 : Domains 19 State := restrict root4Node1Domains2 0 (3,4)
def root4Node2Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,3)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(0,1),(6,4)]
  | 8 => [(1,2),(6,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,3),(1,0),(1,1),(6,1)]
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node2Step1_checked :
    checkReplacement table3 root4Node2Domains0 root4Node2Domains1 = true := by decide
def root4Node2Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,3)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(0,1),(6,4)]
  | 8 => [(1,2),(6,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,3),(1,0)]
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0),(5,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node2Step2_checked :
    checkReplacement table12 root4Node2Domains1 root4Node2Domains2 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
