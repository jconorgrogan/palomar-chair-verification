module

public import SpectreFinite.RadiusFiveRoot2Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable5
public import SpectreFinite.RadiusFiveTable51

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root2Node2Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(5,3)]
  | 7 => [(8,5)]
  | 8 => [(1,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1),(8,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(5,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(5,1),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(8,3)]
  | 50 => [(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(4,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(0,1)]
  | 71 => [(6,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(1,0)]
  | 79 => [(7,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(5,0),(5,3)]
  | 86 => [(4,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => [(8,5)]
  | _ => [(1,0)]
def root2Node2Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(5,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1),(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(5,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(5,1),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(8,3)]
  | 50 => some [(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(4,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,1)]
  | 71 => some [(6,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(1,0)]
  | 79 => some [(7,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,0),(5,3)]
  | 86 => some [(4,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(8,5)]
  | _ => some [(1,0)]
theorem root2Node2Domains3_fast_eq : root2Node2Domains3 = expandDomains root2Node2Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node2Domains3 v = expandDomains root2Node2Domains3Fast v from by decide) v
theorem root2Node2Step3Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq (by decide)
theorem root2Node2Step3Narrowing_checked :
    checkNarrowing table12 root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root2Node2Domains2 root2Node2Domains3 (by
      simp only [List.all_cons, List.all_nil, root2Node2Step3Chunk0_0_checked, root2Node2Step3Chunk0_1_checked, root2Node2Step3Chunk0_2_checked, root2Node2Step3Chunk0_3_checked, root2Node2Step3Chunk0_4_checked, root2Node2Step3Chunk0_5_checked, root2Node2Step3Chunk1_0_checked, root2Node2Step3Chunk1_1_checked, root2Node2Step3Chunk1_2_checked, root2Node2Step3Chunk1_3_checked, root2Node2Step3Chunk1_4_checked, root2Node2Step3Chunk1_5_checked, root2Node2Step3Chunk2_0_checked, root2Node2Step3Chunk2_1_checked, root2Node2Step3Chunk2_2_checked, root2Node2Step3Chunk2_3_checked, root2Node2Step3Chunk2_4_checked, root2Node2Step3Chunk2_5_checked, root2Node2Step3Chunk3_0_checked, root2Node2Step3Chunk3_1_checked, root2Node2Step3Chunk3_2_checked, root2Node2Step3Chunk3_3_checked, root2Node2Step3Chunk3_4_checked, root2Node2Step3Chunk3_5_checked, root2Node2Step3Chunk4_0_checked, root2Node2Step3Chunk4_1_checked, root2Node2Step3Chunk4_2_checked, root2Node2Step3Chunk4_3_checked, root2Node2Step3Chunk4_4_checked, root2Node2Step3Chunk4_5_checked, root2Node2Step3Chunk5_0_checked, root2Node2Step3Chunk5_1_checked, root2Node2Step3Chunk5_2_checked, root2Node2Step3Chunk5_3_checked, root2Node2Step3Chunk5_4_checked, root2Node2Step3Chunk5_5_checked, root2Node2Step3Chunk6_0_checked, root2Node2Step3Chunk6_1_checked, root2Node2Step3Chunk6_2_checked, root2Node2Step3Chunk6_3_checked, root2Node2Step3Chunk6_4_checked, root2Node2Step3Chunk6_5_checked, root2Node2Step3Chunk7_0_checked, root2Node2Step3Chunk7_1_checked, root2Node2Step3Chunk7_2_checked, root2Node2Step3Chunk7_3_checked, root2Node2Step3Chunk7_4_checked, root2Node2Step3Chunk7_5_checked, root2Node2Step3Chunk8_0_checked, root2Node2Step3Chunk8_1_checked, root2Node2Step3Chunk8_2_checked, root2Node2Step3Chunk8_3_checked, root2Node2Step3Chunk8_4_checked, root2Node2Step3Chunk8_5_checked, Bool.true_and])
theorem root2Node2Step3_checked :
    checkReplacement table12 root2Node2Domains2 root2Node2Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root2Node2Domains2 root2Node2Domains3
    root2Node2Domains2Fast root2Node2Domains3Fast
    root2Node2Domains2_fast_eq root2Node2Domains3_fast_eq
    root2Node2Step3Narrowing_checked (by decide)
def root2Node2Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(5,3)]
  | 7 => [(8,5)]
  | 8 => [(1,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(5,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(5,1),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(8,3)]
  | 50 => [(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(4,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(0,1)]
  | 71 => [(6,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(1,0)]
  | 79 => [(7,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(5,0),(5,3)]
  | 86 => [(4,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => [(8,5)]
  | _ => [(1,0)]
def root2Node2Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(5,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(5,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(5,1),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(8,3)]
  | 50 => some [(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(4,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,1)]
  | 71 => some [(6,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(1,0)]
  | 79 => some [(7,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,0),(5,3)]
  | 86 => some [(4,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(8,5)]
  | _ => some [(1,0)]
theorem root2Node2Domains4_fast_eq : root2Node2Domains4 = expandDomains root2Node2Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node2Domains4 v = expandDomains root2Node2Domains4Fast v from by decide) v
theorem root2Node2Step4Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq (by decide)
theorem root2Node2Step4Narrowing_checked :
    checkNarrowing table2 root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkNarrowing_flatten table2Scope [table2Rows0_0,table2Rows0_1,table2Rows0_2,table2Rows0_3,table2Rows0_4,table2Rows0_5,table2Rows1_0,table2Rows1_1,table2Rows1_2,table2Rows1_3,table2Rows1_4,table2Rows1_5,table2Rows2_0,table2Rows2_1,table2Rows2_2,table2Rows2_3,table2Rows2_4,table2Rows2_5,table2Rows3_0,table2Rows3_1,table2Rows3_2,table2Rows3_3,table2Rows3_4,table2Rows3_5,table2Rows4_0,table2Rows4_1,table2Rows4_2,table2Rows4_3,table2Rows4_4,table2Rows4_5,table2Rows5_0,table2Rows5_1,table2Rows5_2,table2Rows5_3,table2Rows5_4,table2Rows5_5,table2Rows6_0,table2Rows6_1,table2Rows6_2,table2Rows6_3,table2Rows6_4,table2Rows6_5,table2Rows7_0,table2Rows7_1,table2Rows7_2,table2Rows7_3,table2Rows7_4,table2Rows7_5,table2Rows8_0,table2Rows8_1,table2Rows8_2,table2Rows8_3,table2Rows8_4,table2Rows8_5]
    root2Node2Domains3 root2Node2Domains4 (by
      simp only [List.all_cons, List.all_nil, root2Node2Step4Chunk0_0_checked, root2Node2Step4Chunk0_1_checked, root2Node2Step4Chunk0_2_checked, root2Node2Step4Chunk0_3_checked, root2Node2Step4Chunk0_4_checked, root2Node2Step4Chunk0_5_checked, root2Node2Step4Chunk1_0_checked, root2Node2Step4Chunk1_1_checked, root2Node2Step4Chunk1_2_checked, root2Node2Step4Chunk1_3_checked, root2Node2Step4Chunk1_4_checked, root2Node2Step4Chunk1_5_checked, root2Node2Step4Chunk2_0_checked, root2Node2Step4Chunk2_1_checked, root2Node2Step4Chunk2_2_checked, root2Node2Step4Chunk2_3_checked, root2Node2Step4Chunk2_4_checked, root2Node2Step4Chunk2_5_checked, root2Node2Step4Chunk3_0_checked, root2Node2Step4Chunk3_1_checked, root2Node2Step4Chunk3_2_checked, root2Node2Step4Chunk3_3_checked, root2Node2Step4Chunk3_4_checked, root2Node2Step4Chunk3_5_checked, root2Node2Step4Chunk4_0_checked, root2Node2Step4Chunk4_1_checked, root2Node2Step4Chunk4_2_checked, root2Node2Step4Chunk4_3_checked, root2Node2Step4Chunk4_4_checked, root2Node2Step4Chunk4_5_checked, root2Node2Step4Chunk5_0_checked, root2Node2Step4Chunk5_1_checked, root2Node2Step4Chunk5_2_checked, root2Node2Step4Chunk5_3_checked, root2Node2Step4Chunk5_4_checked, root2Node2Step4Chunk5_5_checked, root2Node2Step4Chunk6_0_checked, root2Node2Step4Chunk6_1_checked, root2Node2Step4Chunk6_2_checked, root2Node2Step4Chunk6_3_checked, root2Node2Step4Chunk6_4_checked, root2Node2Step4Chunk6_5_checked, root2Node2Step4Chunk7_0_checked, root2Node2Step4Chunk7_1_checked, root2Node2Step4Chunk7_2_checked, root2Node2Step4Chunk7_3_checked, root2Node2Step4Chunk7_4_checked, root2Node2Step4Chunk7_5_checked, root2Node2Step4Chunk8_0_checked, root2Node2Step4Chunk8_1_checked, root2Node2Step4Chunk8_2_checked, root2Node2Step4Chunk8_3_checked, root2Node2Step4Chunk8_4_checked, root2Node2Step4Chunk8_5_checked, Bool.true_and])
theorem root2Node2Step4_checked :
    checkReplacement table2 root2Node2Domains3 root2Node2Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root2Node2Domains3 root2Node2Domains4
    root2Node2Domains3Fast root2Node2Domains4Fast
    root2Node2Domains3_fast_eq root2Node2Domains4_fast_eq
    root2Node2Step4Narrowing_checked (by decide)
def root2Node2Domains5 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(5,3)]
  | 7 => [(8,5)]
  | 8 => [(1,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(5,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(5,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(8,3)]
  | 50 => [(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(4,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(0,1)]
  | 71 => [(6,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(1,0)]
  | 79 => [(7,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(5,0),(5,3)]
  | 86 => [(4,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => [(8,5)]
  | _ => [(1,0)]
def root2Node2Domains5Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(5,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(5,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(5,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(8,3)]
  | 50 => some [(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(4,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,1)]
  | 71 => some [(6,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(1,0)]
  | 79 => some [(7,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,0),(5,3)]
  | 86 => some [(4,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(8,5)]
  | _ => some [(1,0)]
theorem root2Node2Domains5_fast_eq : root2Node2Domains5 = expandDomains root2Node2Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node2Domains5 v = expandDomains root2Node2Domains5Fast v from by decide) v
theorem root2Node2Step5Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq (by decide)
theorem root2Node2Step5Narrowing_checked :
    checkNarrowing table5 root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkNarrowing_flatten table5Scope [table5Rows0_0,table5Rows0_1,table5Rows0_2,table5Rows0_3,table5Rows0_4,table5Rows0_5,table5Rows1_0,table5Rows1_1,table5Rows1_2,table5Rows1_3,table5Rows1_4,table5Rows1_5,table5Rows2_0,table5Rows2_1,table5Rows2_2,table5Rows2_3,table5Rows2_4,table5Rows2_5,table5Rows3_0,table5Rows3_1,table5Rows3_2,table5Rows3_3,table5Rows3_4,table5Rows3_5,table5Rows4_0,table5Rows4_1,table5Rows4_2,table5Rows4_3,table5Rows4_4,table5Rows4_5,table5Rows5_0,table5Rows5_1,table5Rows5_2,table5Rows5_3,table5Rows5_4,table5Rows5_5,table5Rows6_0,table5Rows6_1,table5Rows6_2,table5Rows6_3,table5Rows6_4,table5Rows6_5,table5Rows7_0,table5Rows7_1,table5Rows7_2,table5Rows7_3,table5Rows7_4,table5Rows7_5,table5Rows8_0,table5Rows8_1,table5Rows8_2,table5Rows8_3,table5Rows8_4,table5Rows8_5]
    root2Node2Domains4 root2Node2Domains5 (by
      simp only [List.all_cons, List.all_nil, root2Node2Step5Chunk0_0_checked, root2Node2Step5Chunk0_1_checked, root2Node2Step5Chunk0_2_checked, root2Node2Step5Chunk0_3_checked, root2Node2Step5Chunk0_4_checked, root2Node2Step5Chunk0_5_checked, root2Node2Step5Chunk1_0_checked, root2Node2Step5Chunk1_1_checked, root2Node2Step5Chunk1_2_checked, root2Node2Step5Chunk1_3_checked, root2Node2Step5Chunk1_4_checked, root2Node2Step5Chunk1_5_checked, root2Node2Step5Chunk2_0_checked, root2Node2Step5Chunk2_1_checked, root2Node2Step5Chunk2_2_checked, root2Node2Step5Chunk2_3_checked, root2Node2Step5Chunk2_4_checked, root2Node2Step5Chunk2_5_checked, root2Node2Step5Chunk3_0_checked, root2Node2Step5Chunk3_1_checked, root2Node2Step5Chunk3_2_checked, root2Node2Step5Chunk3_3_checked, root2Node2Step5Chunk3_4_checked, root2Node2Step5Chunk3_5_checked, root2Node2Step5Chunk4_0_checked, root2Node2Step5Chunk4_1_checked, root2Node2Step5Chunk4_2_checked, root2Node2Step5Chunk4_3_checked, root2Node2Step5Chunk4_4_checked, root2Node2Step5Chunk4_5_checked, root2Node2Step5Chunk5_0_checked, root2Node2Step5Chunk5_1_checked, root2Node2Step5Chunk5_2_checked, root2Node2Step5Chunk5_3_checked, root2Node2Step5Chunk5_4_checked, root2Node2Step5Chunk5_5_checked, root2Node2Step5Chunk6_0_checked, root2Node2Step5Chunk6_1_checked, root2Node2Step5Chunk6_2_checked, root2Node2Step5Chunk6_3_checked, root2Node2Step5Chunk6_4_checked, root2Node2Step5Chunk6_5_checked, root2Node2Step5Chunk7_0_checked, root2Node2Step5Chunk7_1_checked, root2Node2Step5Chunk7_2_checked, root2Node2Step5Chunk7_3_checked, root2Node2Step5Chunk7_4_checked, root2Node2Step5Chunk7_5_checked, root2Node2Step5Chunk8_0_checked, root2Node2Step5Chunk8_1_checked, root2Node2Step5Chunk8_2_checked, root2Node2Step5Chunk8_3_checked, root2Node2Step5Chunk8_4_checked, root2Node2Step5Chunk8_5_checked, Bool.true_and])
theorem root2Node2Step5_checked :
    checkReplacement table5 root2Node2Domains4 root2Node2Domains5 = true := by
  exact checkReplacement_of_fast_rest _ root2Node2Domains4 root2Node2Domains5
    root2Node2Domains4Fast root2Node2Domains5Fast
    root2Node2Domains4_fast_eq root2Node2Domains5_fast_eq
    root2Node2Step5Narrowing_checked (by decide)
def root2Node2Domains6 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(5,3)]
  | 7 => [(8,5)]
  | 8 => [(1,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(5,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(5,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(1,4)]
  | 44 => [(0,5)]
  | 45 => [(2,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(8,3)]
  | 50 => [(5,5)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(6,0)]
  | 55 => [(3,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(4,0)]
  | 62 => [(7,3)]
  | 63 => [(8,2)]
  | 64 => [(5,0)]
  | 65 => [(4,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(0,1)]
  | 71 => [(6,2)]
  | 72 => [(8,4)]
  | 73 => [(0,0)]
  | 74 => [(7,2)]
  | 75 => [(4,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(1,0)]
  | 79 => [(7,1)]
  | 80 => [(1,5)]
  | 81 => [(6,1)]
  | 82 => [(5,1)]
  | 83 => [(0,1)]
  | 84 => [(6,2)]
  | 85 => [(5,0)]
  | 86 => [(4,5)]
  | 87 => [(7,0)]
  | 88 => [(8,3)]
  | 89 => [(8,5)]
  | _ => [(1,0)]
def root2Node2Domains6Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(5,3)]
  | 7 => some [(8,5)]
  | 8 => some [(1,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(5,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(5,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(1,4)]
  | 44 => some [(0,5)]
  | 45 => some [(2,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(8,3)]
  | 50 => some [(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(6,0)]
  | 55 => some [(3,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(4,0)]
  | 62 => some [(7,3)]
  | 63 => some [(8,2)]
  | 64 => some [(5,0)]
  | 65 => some [(4,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,1)]
  | 71 => some [(6,2)]
  | 72 => some [(8,4)]
  | 73 => some [(0,0)]
  | 74 => some [(7,2)]
  | 75 => some [(4,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(1,0)]
  | 79 => some [(7,1)]
  | 80 => some [(1,5)]
  | 81 => some [(6,1)]
  | 82 => some [(5,1)]
  | 83 => some [(0,1)]
  | 84 => some [(6,2)]
  | 85 => some [(5,0)]
  | 86 => some [(4,5)]
  | 87 => some [(7,0)]
  | 88 => some [(8,3)]
  | 89 => some [(8,5)]
  | _ => some [(1,0)]
theorem root2Node2Domains6_fast_eq : root2Node2Domains6 = expandDomains root2Node2Domains6Fast := by
  funext v
  exact (show ∀ v : Fin 91, root2Node2Domains6 v = expandDomains root2Node2Domains6Fast v from by decide) v
theorem root2Node2Step6Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_of_fast _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq (by decide)
theorem root2Node2Step6Narrowing_checked :
    checkNarrowing table51 root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root2Node2Domains5 root2Node2Domains6 (by
      simp only [List.all_cons, List.all_nil, root2Node2Step6Chunk0_0_checked, root2Node2Step6Chunk0_1_checked, root2Node2Step6Chunk0_2_checked, root2Node2Step6Chunk0_3_checked, root2Node2Step6Chunk0_4_checked, root2Node2Step6Chunk0_5_checked, root2Node2Step6Chunk1_0_checked, root2Node2Step6Chunk1_1_checked, root2Node2Step6Chunk1_2_checked, root2Node2Step6Chunk1_3_checked, root2Node2Step6Chunk1_4_checked, root2Node2Step6Chunk1_5_checked, root2Node2Step6Chunk2_0_checked, root2Node2Step6Chunk2_1_checked, root2Node2Step6Chunk2_2_checked, root2Node2Step6Chunk2_3_checked, root2Node2Step6Chunk2_4_checked, root2Node2Step6Chunk2_5_checked, root2Node2Step6Chunk3_0_checked, root2Node2Step6Chunk3_1_checked, root2Node2Step6Chunk3_2_checked, root2Node2Step6Chunk3_3_checked, root2Node2Step6Chunk3_4_checked, root2Node2Step6Chunk3_5_checked, root2Node2Step6Chunk4_0_checked, root2Node2Step6Chunk4_1_checked, root2Node2Step6Chunk4_2_checked, root2Node2Step6Chunk4_3_checked, root2Node2Step6Chunk4_4_checked, root2Node2Step6Chunk4_5_checked, root2Node2Step6Chunk5_0_checked, root2Node2Step6Chunk5_1_checked, root2Node2Step6Chunk5_2_checked, root2Node2Step6Chunk5_3_checked, root2Node2Step6Chunk5_4_checked, root2Node2Step6Chunk5_5_checked, root2Node2Step6Chunk6_0_checked, root2Node2Step6Chunk6_1_checked, root2Node2Step6Chunk6_2_checked, root2Node2Step6Chunk6_3_checked, root2Node2Step6Chunk6_4_checked, root2Node2Step6Chunk6_5_checked, root2Node2Step6Chunk7_0_checked, root2Node2Step6Chunk7_1_checked, root2Node2Step6Chunk7_2_checked, root2Node2Step6Chunk7_3_checked, root2Node2Step6Chunk7_4_checked, root2Node2Step6Chunk7_5_checked, root2Node2Step6Chunk8_0_checked, root2Node2Step6Chunk8_1_checked, root2Node2Step6Chunk8_2_checked, root2Node2Step6Chunk8_3_checked, root2Node2Step6Chunk8_4_checked, root2Node2Step6Chunk8_5_checked, Bool.true_and])
theorem root2Node2Step6_checked :
    checkReplacement table51 root2Node2Domains5 root2Node2Domains6 = true := by
  exact checkReplacement_of_fast_rest _ root2Node2Domains5 root2Node2Domains6
    root2Node2Domains5Fast root2Node2Domains6Fast
    root2Node2Domains5_fast_eq root2Node2Domains6_fast_eq
    root2Node2Step6Narrowing_checked (by decide)
theorem root2Node2Leaf_checked :
    checkCover 1 constraints root2Outputs root2Node2Domains6 (.output 0) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
