module

public import SpectreFinite.RadiusTwoRoot7Part4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node27Domains0 : Domains 19 State := restrict root7Node23Domains3 6 (8,1)
def root7Node27Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(8,1)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node27Step1_checked :
    checkReplacement table10 root7Node27Domains0 root7Node27Domains1 = true := by decide
def root7Node27Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(8,1)]
  | 4 => [(1,5)]
  | 5 => [(6,1)]
  | 6 => [(8,1)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(8,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | _ => [(0,2)]
theorem root7Node27Step2_checked :
    checkReplacement table14 root7Node27Domains1 root7Node27Domains2 = true := by decide
theorem root7Node27Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node27Domains2 (.output 13) = true := by decide
def root7Node28Domains0 : Domains 19 State := restrict root7Node0Domains5 1 (1,3)
def root7Node28Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(7,1),(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4),(5,4)]
  | 7 => [(5,0),(5,3),(8,3)]
  | 8 => [(4,5),(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,2),(1,5),(3,5),(5,2),(5,5),(6,5),(7,5),(8,5)]
  | 12 => [(0,0),(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(6,4),(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node28Step1_checked :
    checkReplacement table5 root7Node28Domains0 root7Node28Domains1 = true := by decide
def root7Node28Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2),(5,2),(8,2)]
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
theorem root7Node28Step2_checked :
    checkReplacement table6 root7Node28Domains1 root7Node28Domains2 = true := by decide
def root7Node28Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4),(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2),(5,2),(8,2)]
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
theorem root7Node28Step3_checked :
    checkReplacement table0 root7Node28Domains2 root7Node28Domains3 = true := by decide
def root7Node29Domains0 : Domains 19 State := restrict root7Node28Domains3 0 (2,4)
def root7Node29Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4),(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
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
theorem root7Node29Step1_checked :
    checkReplacement table3 root7Node29Domains0 root7Node29Domains1 = true := by decide
def root7Node29Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4),(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,2),(1,5),(3,5),(6,5),(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(0,5),(1,2),(1,3),(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,5)]
theorem root7Node29Step2_checked :
    checkReplacement table13 root7Node29Domains1 root7Node29Domains2 = true := by decide
def root7Node29Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4),(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3),(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node29Step3_checked :
    checkReplacement table15 root7Node29Domains2 root7Node29Domains3 = true := by decide
def root7Node29Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(7,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(3,4),(5,4)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(0,0)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3),(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node29Step4_checked :
    checkReplacement table1 root7Node29Domains3 root7Node29Domains4 = true := by decide
def root7Node29Domains5 (v : Fin 19) : List State :=
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
  | 15 => [(1,3),(6,3)]
  | 16 => [(6,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node29Step5_checked :
    checkReplacement table2 root7Node29Domains4 root7Node29Domains5 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
