module

public import SpectreFinite.RadiusTwoRoot6Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root6Node2Domains0 : Domains 19 State := restrict root6Node0Domains4 0 (7,0)
def root6Node2Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
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
theorem root6Node2Step1_checked :
    checkReplacement table3 root6Node2Domains0 root6Node2Domains1 = true := by decide
def root6Node2Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(2,1),(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(0,0),(4,0),(5,0),(8,0)]
  | 15 => [(3,2),(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(1,5),(5,1),(5,4),(8,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
theorem root6Node2Step2_checked :
    checkReplacement table12 root6Node2Domains1 root6Node2Domains2 = true := by decide
def root6Node2Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(5,4),(8,4)]
  | _ => [(0,0),(6,4)]
theorem root6Node2Step3_checked :
    checkReplacement table14 root6Node2Domains2 root6Node2Domains3 = true := by decide
def root6Node2Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1),(7,1)]
  | 11 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(5,4),(8,4)]
  | _ => [(0,0),(6,4)]
theorem root6Node2Step4_checked :
    checkReplacement table0 root6Node2Domains3 root6Node2Domains4 = true := by decide
def root6Node2Domains5 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1),(7,1)]
  | 11 => [(0,1),(1,5),(6,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(5,4),(8,4)]
  | _ => [(0,0),(6,4)]
theorem root6Node2Step5_checked :
    checkReplacement table6 root6Node2Domains4 root6Node2Domains5 = true := by decide
def root6Node2Domains6 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1),(7,1)]
  | 11 => [(0,1),(1,5),(6,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0),(6,4)]
theorem root6Node2Step6_checked :
    checkReplacement table13 root6Node2Domains5 root6Node2Domains6 = true := by decide
def root6Node3Domains0 : Domains 19 State := restrict root6Node2Domains6 1 (4,3)
def root6Node3Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5),(3,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1),(7,1)]
  | 11 => [(0,1),(1,5),(6,5),(7,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0),(6,4)]
theorem root6Node3Step1_checked :
    checkReplacement table1 root6Node3Domains0 root6Node3Domains1 = true := by decide
def root6Node3Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5),(3,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1),(7,1)]
  | 11 => [(0,1),(1,5),(6,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0),(8,0)]
  | 15 => [(4,5),(7,3)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0),(6,4)]
theorem root6Node3Step2_checked :
    checkReplacement table6 root6Node3Domains1 root6Node3Domains2 = true := by decide
def root6Node3Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5),(3,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0),(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1),(7,1)]
  | 11 => [(0,1),(1,5),(6,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0)]
theorem root6Node3Step3_checked :
    checkReplacement table15 root6Node3Domains2 root6Node3Domains3 = true := by decide
def root6Node4Domains0 : Domains 19 State := restrict root6Node3Domains3 10 (3,1)
def root6Node4Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5),(6,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1)]
  | 11 => [(0,1)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0)]
theorem root6Node4Step1_checked :
    checkReplacement table6 root6Node4Domains0 root6Node4Domains1 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
