module

public import SpectreFinite.RadiusTwoRoot4Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root4Node3Domains0 : Domains 19 State := restrict root4Node2Domains2 7 (0,1)
def root4Node3Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,3)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(1,0)]
  | 13 => [(3,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node3Step1_checked :
    checkReplacement table12 root4Node3Domains0 root4Node3Domains1 = true := by decide
def root4Node3Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,3)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(1,0)]
  | 13 => [(3,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | _ => [(1,0)]
theorem root4Node3Step2_checked :
    checkReplacement table13 root4Node3Domains1 root4Node3Domains2 = true := by decide
theorem root4Node3Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node3Domains2 (.output 0) = true := by decide
def root4Node4Domains0 : Domains 19 State := restrict root4Node2Domains2 7 (6,4)
def root4Node4Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,3)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(6,4)]
  | 8 => [(1,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,3)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node4Step1_checked :
    checkReplacement table12 root4Node4Domains0 root4Node4Domains1 = true := by decide
def root4Node4Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,3)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(6,4)]
  | 8 => [(1,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,3)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node4Step2_checked :
    checkReplacement table13 root4Node4Domains1 root4Node4Domains2 = true := by decide
def root4Node5Domains0 : Domains 19 State := restrict root4Node4Domains2 17 (5,5)
theorem root4Node5Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node5Domains0 (.output 1) = true := by decide
def root4Node6Domains0 : Domains 19 State := restrict root4Node4Domains2 17 (8,5)
theorem root4Node6Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node6Domains0 (.output 2) = true := by decide
def root4Node7Domains0 : Domains 19 State := restrict root4Node1Domains2 0 (7,4)
def root4Node7Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,1),(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(0,0),(6,3)]
  | 8 => [(3,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(0,3),(1,0),(1,1),(6,1)]
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node7Step1_checked :
    checkReplacement table3 root4Node7Domains0 root4Node7Domains1 = true := by decide
def root4Node7Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,1),(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(0,0),(6,3)]
  | 8 => [(3,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(1,1),(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node7Step2_checked :
    checkReplacement table13 root4Node7Domains1 root4Node7Domains2 = true := by decide
def root4Node8Domains0 : Domains 19 State := restrict root4Node7Domains2 3 (2,1)
def root4Node8Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(2,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(0,0)]
  | 8 => [(3,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node8Step1_checked :
    checkReplacement table7 root4Node8Domains0 root4Node8Domains1 = true := by decide
def root4Node9Domains0 : Domains 19 State := restrict root4Node8Domains1 17 (5,5)
theorem root4Node9Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node9Domains0 (.output 3) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
