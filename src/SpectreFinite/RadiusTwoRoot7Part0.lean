module

public import SpectreFinite.RadiusTwoRoot7Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node0Domains0 : Domains 19 State := domains (7,0)
def root7Node0Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0),(1,3)]
  | 2 => stateChoices
  | 3 => [(7,1),(8,1)]
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => stateChoices
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => stateChoices
  | 14 => stateChoices
  | 15 => stateChoices
  | 16 => stateChoices
  | 17 => stateChoices
  | _ => stateChoices
theorem root7Node0Step1_checked :
    checkReplacement table4 root7Node0Domains0 root7Node0Domains1 = true := by decide
def root7Node0Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0),(1,3)]
  | 2 => stateChoices
  | 3 => [(7,1),(8,1)]
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3),(7,3),(8,3)]
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => stateChoices
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node0Step2_checked :
    checkReplacement table14 root7Node0Domains1 root7Node0Domains2 = true := by decide
def root7Node0Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0),(1,3)]
  | 2 => stateChoices
  | 3 => [(7,1),(8,1)]
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => stateChoices
  | 7 => [(3,0),(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3),(7,3),(8,3)]
  | 11 => stateChoices
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node0Step3_checked :
    checkReplacement table12 root7Node0Domains2 root7Node0Domains3 = true := by decide
def root7Node0Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0),(1,3)]
  | 2 => [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => [(3,4),(4,1),(5,1),(5,4),(8,1)]
  | 7 => [(3,0),(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3),(7,3),(8,3)]
  | 11 => [(0,2),(1,5),(3,5),(5,2),(5,5),(6,5),(7,5),(8,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node0Step4_checked :
    checkReplacement table6 root7Node0Domains3 root7Node0Domains4 = true := by decide
def root7Node0Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0),(1,3)]
  | 2 => [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(1,5),(6,5)]
  | 5 => [(0,4),(6,1)]
  | 6 => [(3,4),(4,1),(5,1),(5,4),(8,1)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3),(7,3),(8,3)]
  | 11 => [(0,2),(1,5),(3,5),(5,2),(5,5),(6,5),(7,5),(8,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node0Step5_checked :
    checkReplacement table3 root7Node0Domains4 root7Node0Domains5 = true := by decide
def root7Node1Domains0 : Domains 19 State := restrict root7Node0Domains5 1 (0,0)
def root7Node1Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2),(7,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,2),(1,5),(3,5),(5,2),(5,5),(6,5),(7,5),(8,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node1Step1_checked :
    checkReplacement table5 root7Node1Domains0 root7Node1Domains1 = true := by decide
def root7Node1Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2),(7,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
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
theorem root7Node1Step2_checked :
    checkReplacement table6 root7Node1Domains1 root7Node1Domains2 = true := by decide
def root7Node1Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,4),(8,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2),(7,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(4,1),(5,1),(8,1)]
  | 7 => [(5,0),(5,3)]
  | 8 => [(4,5),(5,5),(8,5)]
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
theorem root7Node1Step3_checked :
    checkReplacement table3 root7Node1Domains2 root7Node1Domains3 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
