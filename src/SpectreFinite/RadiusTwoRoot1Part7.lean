module

public import SpectreFinite.RadiusTwoRoot1Part6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root1Node28Domains0 : Domains 19 State := restrict root1Node26Domains1 12 (6,3)
def root1Node28Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | _ => [(0,1),(6,4)]
theorem root1Node28Step1_checked :
    checkReplacement table13 root1Node28Domains0 root1Node28Domains1 = true := by decide
def root1Node28Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(4,0)]
  | 15 => [(7,3)]
  | 16 => [(1,1)]
  | 17 => [(5,1)]
  | _ => [(0,1)]
theorem root1Node28Step2_checked :
    checkReplacement table14 root1Node28Domains1 root1Node28Domains2 = true := by decide
theorem root1Node28Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node28Domains2 (.output 14) = true := by decide
def root1Node29Domains0 : Domains 19 State := restrict root1Node17Domains4 2 (8,2)
def root1Node30Domains0 : Domains 19 State := restrict root1Node29Domains0 7 (5,3)
def root1Node31Domains0 : Domains 19 State := restrict root1Node30Domains0 11 (1,5)
def root1Node31Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,0)]
theorem root1Node31Step1_checked :
    checkReplacement table15 root1Node31Domains0 root1Node31Domains1 = true := by decide
def root1Node31Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,0)]
theorem root1Node31Step2_checked :
    checkReplacement table13 root1Node31Domains1 root1Node31Domains2 = true := by decide
theorem root1Node31Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node31Domains2 (.output 15) = true := by decide
def root1Node32Domains0 : Domains 19 State := restrict root1Node30Domains0 11 (7,5)
def root1Node32Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(1,3),(6,3)]
  | 13 => [(7,2),(8,2)]
  | 14 => [(4,0),(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | _ => [(0,1),(6,4)]
theorem root1Node32Step1_checked :
    checkReplacement table15 root1Node32Domains0 root1Node32Domains1 = true := by decide
def root1Node33Domains0 : Domains 19 State := restrict root1Node32Domains1 12 (1,3)
def root1Node33Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,1),(6,4)]
theorem root1Node33Step1_checked :
    checkReplacement table13 root1Node33Domains0 root1Node33Domains1 = true := by decide
def root1Node33Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(8,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(7,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(8,0)]
  | 15 => [(7,3)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(6,4)]
theorem root1Node33Step2_checked :
    checkReplacement table14 root1Node33Domains1 root1Node33Domains2 = true := by decide
theorem root1Node33Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node33Domains2 (.output 16) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
