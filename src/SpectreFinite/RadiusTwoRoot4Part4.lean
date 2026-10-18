module

public import SpectreFinite.RadiusTwoRoot4Part3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root4Node24Domains0 : Domains 19 State := restrict root4Node12Domains4 0 (1,4)
def root4Node24Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(2,5),(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(0,0),(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1),(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node24Step1_checked :
    checkReplacement table0 root4Node24Domains0 root4Node24Domains1 = true := by decide
def root4Node24Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(2,5),(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(0,0),(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1),(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node24Step2_checked :
    checkReplacement table1 root4Node24Domains1 root4Node24Domains2 = true := by decide
def root4Node25Domains0 : Domains 19 State := restrict root4Node24Domains2 3 (2,5)
def root4Node25Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(2,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(0,0)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node25Step1_checked :
    checkReplacement table7 root4Node25Domains0 root4Node25Domains1 = true := by decide
def root4Node26Domains0 : Domains 19 State := restrict root4Node25Domains1 11 (4,2)
def root4Node27Domains0 : Domains 19 State := restrict root4Node26Domains0 17 (5,5)
theorem root4Node27Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node27Domains0 (.output 12) = true := by decide
def root4Node28Domains0 : Domains 19 State := restrict root4Node26Domains0 17 (8,5)
theorem root4Node28Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node28Domains0 (.output 13) = true := by decide
def root4Node29Domains0 : Domains 19 State := restrict root4Node25Domains1 11 (8,2)
def root4Node30Domains0 : Domains 19 State := restrict root4Node29Domains0 17 (5,5)
theorem root4Node30Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node30Domains0 (.output 14) = true := by decide
def root4Node31Domains0 : Domains 19 State := restrict root4Node29Domains0 17 (8,5)
theorem root4Node31Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node31Domains0 (.output 15) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
