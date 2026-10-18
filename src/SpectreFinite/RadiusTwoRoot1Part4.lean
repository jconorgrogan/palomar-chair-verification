module

public import SpectreFinite.RadiusTwoRoot1Part3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root1Node13Domains0 : Domains 19 State := restrict root1Node11Domains0 8 (8,5)
def root1Node13Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(3,2),(4,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,0),(6,1)]
theorem root1Node13Step1_checked :
    checkReplacement table13 root1Node13Domains0 root1Node13Domains1 = true := by decide
def root1Node13Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,0)]
theorem root1Node13Step2_checked :
    checkReplacement table15 root1Node13Domains1 root1Node13Domains2 = true := by decide
theorem root1Node13Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node13Domains2 (.output 6) = true := by decide
def root1Node14Domains0 : Domains 19 State := restrict root1Node10Domains4 7 (8,3)
def root1Node15Domains0 : Domains 19 State := restrict root1Node14Domains0 8 (5,5)
def root1Node15Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(3,2),(4,5)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(0,0),(6,1)]
theorem root1Node15Step1_checked :
    checkReplacement table13 root1Node15Domains0 root1Node15Domains1 = true := by decide
def root1Node15Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1)]
  | 11 => [(0,2)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(3,2)]
  | 16 => [(7,1)]
  | 17 => [(1,5)]
  | _ => [(6,1)]
theorem root1Node15Step2_checked :
    checkReplacement table15 root1Node15Domains1 root1Node15Domains2 = true := by decide
theorem root1Node15Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node15Domains2 (.output 7) = true := by decide
def root1Node16Domains0 : Domains 19 State := restrict root1Node14Domains0 8 (8,5)
def root1Node16Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1),(7,1)]
  | 11 => [(0,2),(6,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(3,2),(4,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,0),(6,1)]
theorem root1Node16Step1_checked :
    checkReplacement table13 root1Node16Domains0 root1Node16Domains1 = true := by decide
def root1Node16Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,1)]
  | 4 => [(0,1)]
  | 5 => [(6,2)]
  | 6 => [(7,4)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(1,3)]
  | 13 => [(8,2)]
  | 14 => [(5,0)]
  | 15 => [(4,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | _ => [(0,0)]
theorem root1Node16Step2_checked :
    checkReplacement table15 root1Node16Domains1 root1Node16Domains2 = true := by decide
theorem root1Node16Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node16Domains2 (.output 8) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
