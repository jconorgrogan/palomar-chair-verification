module

public import SpectreFinite.RadiusTwoRoot4Part2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root4Node15Domains0 : Domains 19 State := restrict root4Node14Domains1 11 (4,2)
def root4Node16Domains0 : Domains 19 State := restrict root4Node15Domains0 17 (5,5)
theorem root4Node16Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node16Domains0 (.output 6) = true := by decide
def root4Node17Domains0 : Domains 19 State := restrict root4Node15Domains0 17 (8,5)
theorem root4Node17Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node17Domains0 (.output 7) = true := by decide
def root4Node18Domains0 : Domains 19 State := restrict root4Node14Domains1 11 (8,2)
def root4Node19Domains0 : Domains 19 State := restrict root4Node18Domains0 17 (5,5)
theorem root4Node19Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node19Domains0 (.output 8) = true := by decide
def root4Node20Domains0 : Domains 19 State := restrict root4Node18Domains0 17 (8,5)
theorem root4Node20Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node20Domains0 (.output 9) = true := by decide
def root4Node21Domains0 : Domains 19 State := restrict root4Node13Domains2 3 (8,5)
def root4Node21Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node21Step1_checked :
    checkReplacement table7 root4Node21Domains0 root4Node21Domains1 = true := by decide
def root4Node21Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(8,5)]
  | 4 => [(1,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | _ => [(1,0)]
theorem root4Node21Step2_checked :
    checkReplacement table13 root4Node21Domains1 root4Node21Domains2 = true := by decide
def root4Node22Domains0 : Domains 19 State := restrict root4Node21Domains2 11 (4,2)
theorem root4Node22Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node22Domains0 (.output 10) = true := by decide
def root4Node23Domains0 : Domains 19 State := restrict root4Node21Domains2 11 (8,2)
theorem root4Node23Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node23Domains0 (.output 11) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
