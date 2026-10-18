module

public import SpectreFinite.RadiusTwoRoot0Part6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root0Node28Domains0 : Domains 19 State := restrict root0Node27Domains1 15 (4,1)
def root0Node28Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(1,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1)]
  | 16 => [(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(7,3)]
theorem root0Node28Step1_checked :
    checkReplacement table14 root0Node28Domains0 root0Node28Domains1 = true := by decide
def root0Node28Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(1,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1)]
  | 16 => [(5,5)]
  | 17 => [(7,0)]
  | _ => [(7,3)]
theorem root0Node28Step2_checked :
    checkReplacement table17 root0Node28Domains1 root0Node28Domains2 = true := by decide
theorem root0Node28Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node28Domains2 (.output 13) = true := by decide
def root0Node29Domains0 : Domains 19 State := restrict root0Node27Domains1 15 (8,1)
def root0Node29Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(1,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(8,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(8,1)]
  | 16 => [(5,5),(8,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node29Step1_checked :
    checkReplacement table14 root0Node29Domains0 root0Node29Domains1 = true := by decide
def root0Node30Domains0 : Domains 19 State := restrict root0Node29Domains1 16 (5,5)
theorem root0Node30Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node30Domains0 (.output 14) = true := by decide
def root0Node31Domains0 : Domains 19 State := restrict root0Node29Domains1 16 (8,5)
theorem root0Node31Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node31Domains0 (.output 15) = true := by decide
def root0Node32Domains0 : Domains 19 State := restrict root0Node26Domains2 7 (6,2)
def root0Node32Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(7,3),(8,3)]
theorem root0Node32Step1_checked :
    checkReplacement table12 root0Node32Domains0 root0Node32Domains1 = true := by decide
def root0Node32Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,1),(8,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node32Step2_checked :
    checkReplacement table17 root0Node32Domains1 root0Node32Domains2 = true := by decide
def root0Node32Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(1,5)]
  | 3 => [(8,2)]
  | 4 => [(5,0)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,4)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(8,1)]
  | 16 => [(4,5)]
  | 17 => [(7,0)]
  | _ => [(8,3)]
theorem root0Node32Step3_checked :
    checkReplacement table14 root0Node32Domains2 root0Node32Domains3 = true := by decide
theorem root0Node32Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node32Domains3 (.output 16) = true := by decide
def root0Node33Domains0 : Domains 19 State := restrict root0Node23Domains2 2 (6,5)
end SpectreFinite.HexSearch.RadiusTwo
