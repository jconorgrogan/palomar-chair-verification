module

public import SpectreFinite.RadiusTwoRoot7Part8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root7Node51Domains0 : Domains 19 State := restrict root7Node49Domains2 15 (6,3)
def root7Node51Domains1 (v : Fin 19) : List State :=
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
  | 15 => [(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | _ => [(0,2)]
theorem root7Node51Step1_checked :
    checkReplacement table14 root7Node51Domains0 root7Node51Domains1 = true := by decide
theorem root7Node51Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node51Domains1 (.output 25) = true := by decide
def root7Node52Domains0 : Domains 19 State := restrict root7Node44Domains2 7 (8,3)
def root7Node53Domains0 : Domains 19 State := restrict root7Node52Domains0 8 (5,5)
def root7Node53Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(8,3)]
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
theorem root7Node53Step1_checked :
    checkReplacement table13 root7Node53Domains0 root7Node53Domains1 = true := by decide
def root7Node53Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(8,3)]
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
theorem root7Node53Step2_checked :
    checkReplacement table15 root7Node53Domains1 root7Node53Domains2 = true := by decide
def root7Node54Domains0 : Domains 19 State := restrict root7Node53Domains2 11 (1,5)
theorem root7Node54Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node54Domains0 (.output 26) = true := by decide
def root7Node55Domains0 : Domains 19 State := restrict root7Node53Domains2 11 (3,5)
theorem root7Node55Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node55Domains0 (.output 27) = true := by decide
def root7Node56Domains0 : Domains 19 State := restrict root7Node52Domains0 8 (8,5)
def root7Node56Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(8,3)]
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
theorem root7Node56Step1_checked :
    checkReplacement table13 root7Node56Domains0 root7Node56Domains1 = true := by decide
def root7Node56Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(8,3)]
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
theorem root7Node56Step2_checked :
    checkReplacement table15 root7Node56Domains1 root7Node56Domains2 = true := by decide
def root7Node57Domains0 : Domains 19 State := restrict root7Node56Domains2 15 (1,3)
def root7Node57Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(8,3)]
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
theorem root7Node57Step1_checked :
    checkReplacement table14 root7Node57Domains0 root7Node57Domains1 = true := by decide
theorem root7Node57Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node57Domains1 (.output 28) = true := by decide
def root7Node58Domains0 : Domains 19 State := restrict root7Node56Domains2 15 (6,3)
def root7Node58Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,1)]
  | 4 => [(6,5)]
  | 5 => [(0,4)]
  | 6 => [(5,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(7,5)]
  | 12 => [(6,3)]
  | 13 => [(7,2)]
  | 14 => [(7,4)]
  | 15 => [(6,3)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | _ => [(0,2)]
theorem root7Node58Step1_checked :
    checkReplacement table14 root7Node58Domains0 root7Node58Domains1 = true := by decide
theorem root7Node58Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node58Domains1 (.output 29) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
