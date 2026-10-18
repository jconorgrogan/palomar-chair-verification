module

public import SpectreFinite.RadiusTwoRoot5Part2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root5Node21Domains0 : Domains 19 State := restrict root5Node19Domains1 12 (6,2)
def root5Node21Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,0)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(3,1)]
  | 6 => [(0,1)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node21Step1_checked :
    checkReplacement table12 root5Node21Domains0 root5Node21Domains1 = true := by decide
theorem root5Node21Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node21Domains1 (.output 10) = true := by decide
def root5Node22Domains0 : Domains 19 State := restrict root5Node16Domains2 5 (7,1)
def root5Node22Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,4),(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(1,5),(6,5)]
  | 7 => [(1,3),(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(0,4),(1,2),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3),(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node22Step1_checked :
    checkReplacement table6 root5Node22Domains0 root5Node22Domains1 = true := by decide
def root5Node23Domains0 : Domains 19 State := restrict root5Node22Domains1 2 (2,4)
def root5Node23Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(6,5)]
  | 7 => [(1,3),(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(0,4),(1,2),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3),(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node23Step1_checked :
    checkReplacement table2 root5Node23Domains0 root5Node23Domains1 = true := by decide
def root5Node24Domains0 : Domains 19 State := restrict root5Node23Domains1 7 (1,3)
def root5Node24Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(6,5)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node24Step1_checked :
    checkReplacement table12 root5Node24Domains0 root5Node24Domains1 = true := by decide
theorem root5Node24Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node24Domains1 (.output 11) = true := by decide
def root5Node25Domains0 : Domains 19 State := restrict root5Node23Domains1 7 (7,3)
def root5Node25Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(6,5)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(1,2),(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node25Step1_checked :
    checkReplacement table12 root5Node25Domains0 root5Node25Domains1 = true := by decide
def root5Node26Domains0 : Domains 19 State := restrict root5Node25Domains1 12 (1,2)
def root5Node26Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(6,5)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node26Step1_checked :
    checkReplacement table12 root5Node26Domains0 root5Node26Domains1 = true := by decide
theorem root5Node26Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node26Domains1 (.output 12) = true := by decide
def root5Node27Domains0 : Domains 19 State := restrict root5Node25Domains1 12 (6,2)
def root5Node27Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(6,5)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node27Step1_checked :
    checkReplacement table12 root5Node27Domains0 root5Node27Domains1 = true := by decide
theorem root5Node27Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node27Domains1 (.output 13) = true := by decide
def root5Node28Domains0 : Domains 19 State := restrict root5Node22Domains1 2 (4,4)
def root5Node28Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(1,5)]
  | 7 => [(1,3),(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(0,4),(1,2),(6,2)]
  | 13 => [(5,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3),(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node28Step1_checked :
    checkReplacement table2 root5Node28Domains0 root5Node28Domains1 = true := by decide
def root5Node29Domains0 : Domains 19 State := restrict root5Node28Domains1 7 (1,3)
def root5Node29Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(1,5)]
  | 7 => [(1,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,3)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node29Step1_checked :
    checkReplacement table12 root5Node29Domains0 root5Node29Domains1 = true := by decide
theorem root5Node29Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node29Domains1 (.output 14) = true := by decide
def root5Node30Domains0 : Domains 19 State := restrict root5Node28Domains1 7 (7,3)
def root5Node30Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(1,5)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(7,0)]
  | 12 => [(1,2),(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,1),(8,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root5Node30Step1_checked :
    checkReplacement table12 root5Node30Domains0 root5Node30Domains1 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
