module

public import SpectreFinite.RadiusTwoRoot8Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root8Node12Domains0 : Domains 19 State := restrict root8Node11Domains1 17 (3,5)
theorem root8Node12Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node12Domains0 (.output 4) = true := by decide
def root8Node13Domains0 : Domains 19 State := restrict root8Node11Domains1 17 (7,5)
theorem root8Node13Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node13Domains0 (.output 5) = true := by decide
def root8Node14Domains0 : Domains 19 State := restrict root8Node10Domains0 12 (6,2)
def root8Node14Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(5,1)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(5,5)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(6,0)]
theorem root8Node14Step1_checked :
    checkReplacement table12 root8Node14Domains0 root8Node14Domains1 = true := by decide
def root8Node14Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(5,1)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(5,5)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4)]
  | 15 => [(0,5)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(6,0)]
theorem root8Node14Step2_checked :
    checkReplacement table13 root8Node14Domains1 root8Node14Domains2 = true := by decide
def root8Node15Domains0 : Domains 19 State := restrict root8Node14Domains2 7 (3,3)
theorem root8Node15Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node15Domains0 (.output 6) = true := by decide
def root8Node16Domains0 : Domains 19 State := restrict root8Node14Domains2 7 (7,3)
theorem root8Node16Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node16Domains0 (.output 7) = true := by decide
def root8Node17Domains0 : Domains 19 State := restrict root8Node9Domains2 6 (8,1)
def root8Node18Domains0 : Domains 19 State := restrict root8Node17Domains0 12 (0,4)
def root8Node18Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(8,1)]
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
theorem root8Node18Step1_checked :
    checkReplacement table12 root8Node18Domains0 root8Node18Domains1 = true := by decide
def root8Node19Domains0 : Domains 19 State := restrict root8Node18Domains1 17 (3,5)
theorem root8Node19Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node19Domains0 (.output 8) = true := by decide
def root8Node20Domains0 : Domains 19 State := restrict root8Node18Domains1 17 (7,5)
theorem root8Node20Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node20Domains0 (.output 9) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
