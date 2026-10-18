module

public import SpectreFinite.RadiusTwoRoot6Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root6Node0Domains0 : Domains 19 State := domains (6,0)
def root6Node0Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0),(8,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => stateChoices
  | 3 => [(0,4),(4,4),(5,4),(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(2,5),(3,5),(7,5)]
  | 9 => [(6,0)]
  | 10 => stateChoices
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => stateChoices
  | 14 => stateChoices
  | 15 => stateChoices
  | 16 => stateChoices
  | 17 => stateChoices
  | _ => stateChoices
theorem root6Node0Step1_checked :
    checkReplacement table4 root6Node0Domains0 root6Node0Domains1 = true := by decide
def root6Node0Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0),(8,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => stateChoices
  | 3 => [(0,4),(4,4),(5,4),(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => stateChoices
  | 7 => stateChoices
  | 8 => [(2,5),(3,5),(7,5)]
  | 9 => [(6,0)]
  | 10 => [(2,1),(3,1),(7,1)]
  | 11 => stateChoices
  | 12 => stateChoices
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => stateChoices
  | 17 => [(1,5),(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root6Node0Step2_checked :
    checkReplacement table14 root6Node0Domains1 root6Node0Domains2 = true := by decide
def root6Node0Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0),(8,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(0,4),(4,4),(5,4),(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => stateChoices
  | 8 => [(2,5),(3,5),(7,5)]
  | 9 => [(6,0)]
  | 10 => [(2,1),(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => stateChoices
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => stateChoices
  | 17 => [(1,5),(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root6Node0Step3_checked :
    checkReplacement table6 root6Node0Domains2 root6Node0Domains3 = true := by decide
def root6Node0Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0),(8,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(0,4),(4,4),(5,4),(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(3,0),(4,3),(7,1)]
  | 8 => [(2,5),(3,5),(7,5)]
  | 9 => [(6,0)]
  | 10 => [(2,1),(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(1,2),(6,1),(6,2),(7,1)]
  | 17 => [(1,5),(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root6Node0Step4_checked :
    checkReplacement table12 root6Node0Domains3 root6Node0Domains4 = true := by decide
def root6Node1Domains0 : Domains 19 State := restrict root6Node0Domains4 0 (4,2)
def root6Node1Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(0,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(3,0)]
  | 8 => [(2,5)]
  | 9 => [(6,0)]
  | 10 => [(2,1),(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 13 => [(4,4),(7,2),(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(1,2),(6,1),(6,2),(7,1)]
  | 17 => [(1,5),(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root6Node1Step1_checked :
    checkReplacement table3 root6Node1Domains0 root6Node1Domains1 = true := by decide
def root6Node1Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(0,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(3,0)]
  | 8 => [(2,5)]
  | 9 => [(6,0)]
  | 10 => [(2,1),(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root6Node1Step2_checked :
    checkReplacement table13 root6Node1Domains1 root6Node1Domains2 = true := by decide
def root6Node1Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(0,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(3,0)]
  | 8 => [(2,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root6Node1Step3_checked :
    checkReplacement table15 root6Node1Domains2 root6Node1Domains3 = true := by decide
def root6Node1Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(0,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(3,0)]
  | 8 => [(2,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root6Node1Step4_checked :
    checkReplacement table1 root6Node1Domains3 root6Node1Domains4 = true := by decide
def root6Node1Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(0,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(3,0)]
  | 8 => [(2,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root6Node1Step5_checked :
    checkReplacement table2 root6Node1Domains4 root6Node1Domains5 = true := by decide
theorem root6Node1Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node1Domains5 (.output 0) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
