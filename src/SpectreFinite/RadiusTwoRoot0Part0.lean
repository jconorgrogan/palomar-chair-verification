module

public import SpectreFinite.RadiusTwoRoot0Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node0Domains0 : Domains 19 State := domains (0,0)
def root0Node0Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => [(1,0),(3,0),(5,0),(6,0)]
  | 5 => [(2,1),(2,5),(4,5)]
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(4,4),(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(2,2),(3,2),(7,2)]
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => stateChoices
  | 16 => stateChoices
  | 17 => stateChoices
  | _ => stateChoices
theorem root0Node0Step1_checked :
    checkReplacement table9 root0Node0Domains0 root0Node0Domains1 = true := by decide
def root0Node0Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => [(1,0),(3,0),(5,0),(6,0)]
  | 5 => [(2,1),(2,5),(4,5)]
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(4,4),(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(2,2),(3,2),(7,2)]
  | 11 => stateChoices
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => stateChoices
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(3,0),(7,0)]
  | _ => stateChoices
theorem root0Node0Step2_checked :
    checkReplacement table13 root0Node0Domains1 root0Node0Domains2 = true := by decide
def root0Node0Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => [(1,0),(3,0),(5,0),(6,0)]
  | 5 => [(2,1),(2,5),(4,5)]
  | 6 => stateChoices
  | 7 => stateChoices
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
theorem root0Node0Step3_checked :
    checkReplacement table15 root0Node0Domains2 root0Node0Domains3 = true := by decide
def root0Node0Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(0,2),(1,0),(1,4),(1,5),(6,0),(6,5)]
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => [(3,5),(5,2),(5,5),(8,2)]
  | 4 => [(1,0),(3,0),(5,0),(6,0)]
  | 5 => [(2,1),(2,5),(4,5)]
  | 6 => stateChoices
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
theorem root0Node0Step4_checked :
    checkReplacement table3 root0Node0Domains3 root0Node0Domains4 = true := by decide
def root0Node0Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(0,2),(1,0),(1,4),(1,5),(6,0),(6,5)]
  | 1 => [(0,4),(0,5),(1,1),(3,1),(6,1),(6,2),(7,1)]
  | 2 => [(0,1),(1,4),(1,5),(2,4),(6,4),(6,5),(7,4)]
  | 3 => [(3,5),(5,2),(5,5),(8,2)]
  | 4 => [(1,0),(3,0),(5,0),(6,0)]
  | 5 => [(2,1),(2,5),(4,5)]
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
theorem root0Node0Step5_checked :
    checkReplacement table2 root0Node0Domains4 root0Node0Domains5 = true := by decide
def root0Node1Domains0 : Domains 19 State := restrict root0Node0Domains5 5 (2,1)
def root0Node1Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(0,2),(1,0),(1,4),(1,5),(6,0),(6,5)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(2,4),(7,4)]
  | 3 => [(3,5),(5,2),(5,5),(8,2)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(2,1)]
  | 6 => [(0,2)]
  | 7 => [(0,4),(0,5),(1,2),(6,2)]
  | 8 => [(4,4),(5,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(3,3),(4,0),(7,4)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(0,1),(4,1),(5,1),(8,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(3,0),(7,0)]
  | _ => [(4,5),(7,3),(8,3)]
theorem root0Node1Step1_checked :
    checkReplacement table5 root0Node1Domains0 root0Node1Domains1 = true := by decide
def root0Node1Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(2,4),(7,4)]
  | 3 => [(3,5),(5,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(2,1)]
  | 6 => [(0,2)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(3,3),(4,0),(7,4)]
  | 12 => [(4,3),(7,1),(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(0,1),(4,1),(5,1),(8,1)]
  | 16 => [(0,5),(4,5),(5,5),(8,5)]
  | 17 => [(2,0),(3,0),(7,0)]
  | _ => [(4,5),(7,3),(8,3)]
theorem root0Node1Step2_checked :
    checkReplacement table3 root0Node1Domains1 root0Node1Domains2 = true := by decide
def root0Node1Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(2,4),(7,4)]
  | 3 => [(3,5),(5,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(2,1)]
  | 6 => [(0,2)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(3,3),(4,0),(7,4)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(0,1),(4,1),(5,1),(8,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(4,5),(7,3),(8,3)]
theorem root0Node1Step3_checked :
    checkReplacement table13 root0Node1Domains2 root0Node1Domains3 = true := by decide
def root0Node1Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(2,4),(7,4)]
  | 3 => [(3,5),(5,5)]
  | 4 => [(1,0),(6,0)]
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
theorem root0Node1Step4_checked :
    checkReplacement table15 root0Node1Domains3 root0Node1Domains4 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
