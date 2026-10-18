module

public import SpectreFinite.RadiusTwoRoot7Part5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node30Domains0 : Domains 19 State := restrict root7Node29Domains5 15 (1,3)
def root7Node30Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | _ => [(6,5)]
theorem root7Node30Step1_checked :
    checkReplacement table14 root7Node30Domains0 root7Node30Domains1 = true := by decide
theorem root7Node30Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node30Domains1 (.output 14) = true := by decide
def root7Node31Domains0 : Domains 19 State := restrict root7Node29Domains5 15 (6,3)
def root7Node31Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1)]
  | _ => [(0,2)]
theorem root7Node31Step1_checked :
    checkReplacement table14 root7Node31Domains0 root7Node31Domains1 = true := by decide
theorem root7Node31Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node31Domains1 (.output 15) = true := by decide
def root7Node32Domains0 : Domains 19 State := restrict root7Node28Domains3 0 (7,4)
def root7Node32Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2),(8,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4),(5,4)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,2),(1,5),(3,5),(6,5),(7,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node32Step1_checked :
    checkReplacement table1 root7Node32Domains0 root7Node32Domains1 = true := by decide
def root7Node33Domains0 : Domains 19 State := restrict root7Node32Domains1 2 (4,2)
def root7Node33Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node33Step1_checked :
    checkReplacement table6 root7Node33Domains0 root7Node33Domains1 = true := by decide
def root7Node33Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,3),(6,0)]
theorem root7Node33Step2_checked :
    checkReplacement table15 root7Node33Domains1 root7Node33Domains2 = true := by decide
def root7Node33Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3),(6,0)]
theorem root7Node33Step3_checked :
    checkReplacement table13 root7Node33Domains2 root7Node33Domains3 = true := by decide
def root7Node33Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(0,5),(1,2)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3),(6,0)]
theorem root7Node33Step4_checked :
    checkReplacement table3 root7Node33Domains3 root7Node33Domains4 = true := by decide
def root7Node34Domains0 : Domains 19 State := restrict root7Node33Domains4 7 (5,3)
def root7Node35Domains0 : Domains 19 State := restrict root7Node34Domains0 10 (2,3)
def root7Node35Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3)]
  | 11 => [(0,2)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3)]
theorem root7Node35Step1_checked :
    checkReplacement table15 root7Node35Domains0 root7Node35Domains1 = true := by decide
theorem root7Node35Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node35Domains1 (.output 16) = true := by decide
def root7Node36Domains0 : Domains 19 State := restrict root7Node34Domains0 10 (4,3)
def root7Node36Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(6,0)]
theorem root7Node36Step1_checked :
    checkReplacement table15 root7Node36Domains0 root7Node36Domains1 = true := by decide
theorem root7Node36Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node36Domains1 (.output 17) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
