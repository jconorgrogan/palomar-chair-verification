module

public import SpectreFinite.RadiusTwoRoot6Part4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root6Node27Domains0 : Domains 19 State := restrict root6Node26Domains1 12 (1,3)
def root6Node27Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,1),(6,4)]
theorem root6Node27Step1_checked :
    checkReplacement table13 root6Node27Domains0 root6Node27Domains1 = true := by decide
def root6Node27Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(6,4)]
theorem root6Node27Step2_checked :
    checkReplacement table14 root6Node27Domains1 root6Node27Domains2 = true := by decide
theorem root6Node27Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node27Domains2 (.output 13) = true := by decide
def root6Node28Domains0 : Domains 19 State := restrict root6Node26Domains1 12 (6,3)
def root6Node28Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | _ => [(0,1),(6,4)]
theorem root6Node28Step1_checked :
    checkReplacement table13 root6Node28Domains0 root6Node28Domains1 = true := by decide
def root6Node28Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(5,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root6Node28Step2_checked :
    checkReplacement table14 root6Node28Domains1 root6Node28Domains2 = true := by decide
theorem root6Node28Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node28Domains2 (.output 14) = true := by decide
def root6Node29Domains0 : Domains 19 State := restrict root6Node23Domains5 3 (8,4)
def root6Node29Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(4,0),(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(0,4),(1,1),(1,2),(6,2)]
  | 17 => [(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,4)]
theorem root6Node29Step1_checked :
    checkReplacement table8 root6Node29Domains0 root6Node29Domains1 = true := by decide
def root6Node29Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0),(0,1),(6,4)]
theorem root6Node29Step2_checked :
    checkReplacement table13 root6Node29Domains1 root6Node29Domains2 = true := by decide
def root6Node29Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0),(6,4)]
theorem root6Node29Step3_checked :
    checkReplacement table14 root6Node29Domains2 root6Node29Domains3 = true := by decide
def root6Node30Domains0 : Domains 19 State := restrict root6Node29Domains3 11 (1,5)
def root6Node30Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(8,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0)]
theorem root6Node30Step1_checked :
    checkReplacement table15 root6Node30Domains0 root6Node30Domains1 = true := by decide
def root6Node31Domains0 : Domains 19 State := restrict root6Node30Domains1 16 (1,2)
theorem root6Node31Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node31Domains0 (.output 15) = true := by decide
def root6Node32Domains0 : Domains 19 State := restrict root6Node30Domains1 16 (6,2)
theorem root6Node32Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node32Domains0 (.output 16) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
