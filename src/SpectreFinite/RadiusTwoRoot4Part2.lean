module

public import SpectreFinite.RadiusTwoRoot4Part1

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root4Node10Domains0 : Domains 19 State := restrict root4Node8Domains1 17 (8,5)
theorem root4Node10Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node10Domains0 (.output 4) = true := by decide
def root4Node11Domains0 : Domains 19 State := restrict root4Node7Domains2 3 (4,1)
def root4Node11Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(6,3)]
  | 8 => [(3,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node11Step1_checked :
    checkReplacement table7 root4Node11Domains0 root4Node11Domains1 = true := by decide
def root4Node11Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,1)]
  | 4 => [(0,2)]
  | 5 => [(1,1)]
  | 6 => [(4,1)]
  | 7 => [(6,3)]
  | 8 => [(3,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(5,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | _ => [(1,0)]
theorem root4Node11Step2_checked :
    checkReplacement table13 root4Node11Domains1 root4Node11Domains2 = true := by decide
theorem root4Node11Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node11Domains2 (.output 5) = true := by decide
def root4Node12Domains0 : Domains 19 State := restrict root4Node0Domains5 5 (7,1)
def root4Node12Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(2,5),(4,5),(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(7,1)]
  | 6 => [(4,1),(7,5)]
  | 7 => [(0,0),(0,1),(6,3),(6,4)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(5,2),(8,2)]
  | 12 => [(0,3),(1,0),(1,1),(6,1)]
  | 13 => [(3,1),(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node12Step1_checked :
    checkReplacement table4 root4Node12Domains0 root4Node12Domains1 = true := by decide
def root4Node12Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(2,5),(4,5),(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(7,1)]
  | 6 => [(4,1),(7,5)]
  | 7 => [(0,0),(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(5,2),(8,2)]
  | 12 => [(1,1),(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node12Step2_checked :
    checkReplacement table12 root4Node12Domains1 root4Node12Domains2 = true := by decide
def root4Node12Domains3 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(2,5),(4,5),(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(0,0),(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1),(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node12Step3_checked :
    checkReplacement table6 root4Node12Domains2 root4Node12Domains3 = true := by decide
def root4Node12Domains4 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(2,5),(4,5),(7,5),(8,5)]
  | 4 => [(1,0),(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(0,0),(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1),(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node12Step4_checked :
    checkReplacement table13 root4Node12Domains3 root4Node12Domains4 = true := by decide
def root4Node13Domains0 : Domains 19 State := restrict root4Node12Domains4 0 (0,1)
def root4Node13Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(4,5),(8,5)]
  | 4 => [(1,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(0,0),(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1),(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node13Step1_checked :
    checkReplacement table0 root4Node13Domains0 root4Node13Domains1 = true := by decide
def root4Node13Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(4,5),(8,5)]
  | 4 => [(1,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(0,0),(6,3)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(1,1),(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node13Step2_checked :
    checkReplacement table1 root4Node13Domains1 root4Node13Domains2 = true := by decide
def root4Node14Domains0 : Domains 19 State := restrict root4Node13Domains2 3 (4,5)
def root4Node14Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(4,5)]
  | 4 => [(1,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(0,0)]
  | 8 => [(7,2)]
  | 9 => [(4,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(6,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | _ => [(1,0)]
theorem root4Node14Step1_checked :
    checkReplacement table7 root4Node14Domains0 root4Node14Domains1 = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
