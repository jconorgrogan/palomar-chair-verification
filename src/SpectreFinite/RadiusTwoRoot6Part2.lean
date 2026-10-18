module

public import SpectreFinite.RadiusTwoRoot6Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root6Node5Domains0 : Domains 19 State := restrict root6Node4Domains1 2 (1,5)
def root6Node6Domains0 : Domains 19 State := restrict root6Node5Domains0 16 (1,2)
theorem root6Node6Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node6Domains0 (.output 1) = true := by decide
def root6Node7Domains0 : Domains 19 State := restrict root6Node5Domains0 16 (6,2)
theorem root6Node7Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node7Domains0 (.output 2) = true := by decide
def root6Node8Domains0 : Domains 19 State := restrict root6Node4Domains1 2 (6,5)
def root6Node9Domains0 : Domains 19 State := restrict root6Node8Domains0 16 (1,2)
theorem root6Node9Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node9Domains0 (.output 3) = true := by decide
def root6Node10Domains0 : Domains 19 State := restrict root6Node8Domains0 16 (6,2)
theorem root6Node10Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node10Domains0 (.output 4) = true := by decide
def root6Node11Domains0 : Domains 19 State := restrict root6Node3Domains3 10 (7,1)
def root6Node11Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,4),(4,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5),(6,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0)]
theorem root6Node11Step1_checked :
    checkReplacement table6 root6Node11Domains0 root6Node11Domains1 = true := by decide
def root6Node12Domains0 : Domains 19 State := restrict root6Node11Domains1 6 (2,4)
def root6Node12Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(4,4)]
  | 4 => [(1,4)]
  | 5 => [(0,5)]
  | 6 => [(2,4)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(7,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | _ => [(0,0)]
theorem root6Node12Step1_checked :
    checkReplacement table6 root6Node12Domains0 root6Node12Domains1 = true := by decide
def root6Node13Domains0 : Domains 19 State := restrict root6Node12Domains1 16 (1,2)
theorem root6Node13Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node13Domains0 (.output 5) = true := by decide
def root6Node14Domains0 : Domains 19 State := restrict root6Node12Domains1 16 (6,2)
theorem root6Node14Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node14Domains0 (.output 6) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
