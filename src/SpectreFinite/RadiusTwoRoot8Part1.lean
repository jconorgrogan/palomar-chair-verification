module

public import SpectreFinite.RadiusTwoRoot8Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root8Node4Domains0 : Domains 19 State := restrict root8Node3Domains1 17 (3,5)
theorem root8Node4Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node4Domains0 (.output 0) = true := by decide
def root8Node5Domains0 : Domains 19 State := restrict root8Node3Domains1 17 (7,5)
theorem root8Node5Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node5Domains0 (.output 1) = true := by decide
def root8Node6Domains0 : Domains 19 State := restrict root8Node2Domains2 12 (6,2)
def root8Node6Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3)]
theorem root8Node6Step1_checked :
    checkReplacement table12 root8Node6Domains0 root8Node6Domains1 = true := by decide
def root8Node6Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3)]
theorem root8Node6Step2_checked :
    checkReplacement table13 root8Node6Domains1 root8Node6Domains2 = true := by decide
def root8Node7Domains0 : Domains 19 State := restrict root8Node6Domains2 7 (3,3)
theorem root8Node7Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node7Domains0 (.output 2) = true := by decide
def root8Node8Domains0 : Domains 19 State := restrict root8Node6Domains2 7 (7,3)
theorem root8Node8Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node8Domains0 (.output 3) = true := by decide
def root8Node9Domains0 : Domains 19 State := restrict root8Node1Domains2 10 (8,3)
def root8Node9Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(5,1),(8,1)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(5,5)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3),(6,0)]
theorem root8Node9Step1_checked :
    checkReplacement table10 root8Node9Domains0 root8Node9Domains1 = true := by decide
def root8Node9Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(5,1),(8,1)]
  | 7 => [(1,3),(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(5,5)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(6,0)]
theorem root8Node9Step2_checked :
    checkReplacement table14 root8Node9Domains1 root8Node9Domains2 = true := by decide
def root8Node10Domains0 : Domains 19 State := restrict root8Node9Domains2 6 (5,1)
def root8Node11Domains0 : Domains 19 State := restrict root8Node10Domains0 12 (0,4)
def root8Node11Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(5,1)]
  | 7 => [(1,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(5,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(4,3)]
  | 17 => [(3,5),(7,5)]
  | _ => [(6,0)]
theorem root8Node11Step1_checked :
    checkReplacement table12 root8Node11Domains0 root8Node11Domains1 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
