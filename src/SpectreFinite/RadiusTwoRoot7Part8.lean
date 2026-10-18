module

public import SpectreFinite.RadiusTwoRoot7Part7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node44Domains0 : Domains 19 State := restrict root7Node40Domains2 3 (8,1)
def root7Node44Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5),(3,5),(7,5)]
  | 12 => [(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(7,4)]
  | 15 => [(0,5),(1,3),(6,3)]
  | 16 => [(1,1),(6,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
theorem root7Node44Step1_checked :
    checkReplacement table7 root7Node44Domains0 root7Node44Domains1 = true := by decide
def root7Node44Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5),(3,5),(7,5)]
  | 12 => [(0,5),(6,3)]
  | 13 => [(4,4),(7,2)]
  | 14 => [(1,4),(7,4)]
  | 15 => [(0,5),(1,3),(6,3)]
  | 16 => [(1,1),(7,1)]
  | 17 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
theorem root7Node44Step2_checked :
    checkReplacement table12 root7Node44Domains1 root7Node44Domains2 = true := by decide
def root7Node45Domains0 : Domains 19 State := restrict root7Node44Domains2 7 (5,3)
def root7Node46Domains0 : Domains 19 State := restrict root7Node45Domains0 8 (5,5)
def root7Node46Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5),(3,5),(7,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5),(1,3),(6,3)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,2),(6,0),(6,5)]
theorem root7Node46Step1_checked :
    checkReplacement table13 root7Node46Domains0 root7Node46Domains1 = true := by decide
def root7Node46Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5),(3,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(6,0)]
theorem root7Node46Step2_checked :
    checkReplacement table15 root7Node46Domains1 root7Node46Domains2 = true := by decide
def root7Node47Domains0 : Domains 19 State := restrict root7Node46Domains2 11 (1,5)
theorem root7Node47Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node47Domains0 (.output 22) = true := by decide
def root7Node48Domains0 : Domains 19 State := restrict root7Node46Domains2 11 (3,5)
theorem root7Node48Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node48Domains0 (.output 23) = true := by decide
def root7Node49Domains0 : Domains 19 State := restrict root7Node45Domains0 8 (8,5)
def root7Node49Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5),(3,5),(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(0,5),(1,3),(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
theorem root7Node49Step1_checked :
    checkReplacement table13 root7Node49Domains0 root7Node49Domains1 = true := by decide
def root7Node49Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3),(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
theorem root7Node49Step2_checked :
    checkReplacement table15 root7Node49Domains1 root7Node49Domains2 = true := by decide
def root7Node50Domains0 : Domains 19 State := restrict root7Node49Domains2 15 (1,3)
def root7Node50Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(1,3)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | _ => [(6,5)]
theorem root7Node50Step1_checked :
    checkReplacement table14 root7Node50Domains0 root7Node50Domains1 = true := by decide
theorem root7Node50Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node50Domains1 (.output 24) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
