module

public import SpectreFinite.RadiusTwoRoot8Part5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root8Node40Domains0 : Domains 19 State := restrict root8Node32Domains2 7 (7,3)
def root8Node40Domains1 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(7,1)]
  | 17 => [(3,5),(7,5)]
  | _ => [(0,3)]
theorem root8Node40Step1_checked :
    checkReplacement table12 root8Node40Domains0 root8Node40Domains1 = true := by decide
def root8Node40Domains2 (v : Fin 19) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(7,5)]
  | 4 => [(6,0)]
  | 5 => [(7,1)]
  | 6 => [(7,5)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(4,2),(8,2)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(6,4)]
  | 15 => [(1,2)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | _ => [(0,3)]
theorem root8Node40Step2_checked :
    checkReplacement table13 root8Node40Domains1 root8Node40Domains2 = true := by decide
def root8Node41Domains0 : Domains 19 State := restrict root8Node40Domains2 11 (4,2)
theorem root8Node41Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node41Domains0 (.output 20) = true := by decide
def root8Node42Domains0 : Domains 19 State := restrict root8Node40Domains2 11 (8,2)
theorem root8Node42Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node42Domains0 (.output 21) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
