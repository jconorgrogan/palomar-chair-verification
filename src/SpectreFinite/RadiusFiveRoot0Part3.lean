module

public import SpectreFinite.RadiusFiveRoot0Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable21
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable44
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node2Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(8,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(6,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(5,2)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(5,2)]
  | 50 => [(5,0)]
  | 51 => [(7,1)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(7,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(1,2)]
  | 71 => [(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(8,2)]
  | 77 => [(5,0)]
  | 78 => [(8,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(5,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(5,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node2Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(6,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(5,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(1,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(5,0)]
  | 78 => some [(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(5,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node2Domains4_fast_eq : root0Node2Domains4 = expandDomains root0Node2Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node2Domains4 v = expandDomains root0Node2Domains4Fast v from by decide) v
theorem root0Node2Step4Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq (by decide)
theorem root0Node2Step4Narrowing_checked :
    checkNarrowing table21 root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root0Node2Domains3 root0Node2Domains4 (by
      simp only [List.all_cons, List.all_nil, root0Node2Step4Chunk0_0_checked, root0Node2Step4Chunk0_1_checked, root0Node2Step4Chunk0_2_checked, root0Node2Step4Chunk0_3_checked, root0Node2Step4Chunk0_4_checked, root0Node2Step4Chunk0_5_checked, root0Node2Step4Chunk1_0_checked, root0Node2Step4Chunk1_1_checked, root0Node2Step4Chunk1_2_checked, root0Node2Step4Chunk1_3_checked, root0Node2Step4Chunk1_4_checked, root0Node2Step4Chunk1_5_checked, root0Node2Step4Chunk2_0_checked, root0Node2Step4Chunk2_1_checked, root0Node2Step4Chunk2_2_checked, root0Node2Step4Chunk2_3_checked, root0Node2Step4Chunk2_4_checked, root0Node2Step4Chunk2_5_checked, root0Node2Step4Chunk3_0_checked, root0Node2Step4Chunk3_1_checked, root0Node2Step4Chunk3_2_checked, root0Node2Step4Chunk3_3_checked, root0Node2Step4Chunk3_4_checked, root0Node2Step4Chunk3_5_checked, root0Node2Step4Chunk4_0_checked, root0Node2Step4Chunk4_1_checked, root0Node2Step4Chunk4_2_checked, root0Node2Step4Chunk4_3_checked, root0Node2Step4Chunk4_4_checked, root0Node2Step4Chunk4_5_checked, root0Node2Step4Chunk5_0_checked, root0Node2Step4Chunk5_1_checked, root0Node2Step4Chunk5_2_checked, root0Node2Step4Chunk5_3_checked, root0Node2Step4Chunk5_4_checked, root0Node2Step4Chunk5_5_checked, root0Node2Step4Chunk6_0_checked, root0Node2Step4Chunk6_1_checked, root0Node2Step4Chunk6_2_checked, root0Node2Step4Chunk6_3_checked, root0Node2Step4Chunk6_4_checked, root0Node2Step4Chunk6_5_checked, root0Node2Step4Chunk7_0_checked, root0Node2Step4Chunk7_1_checked, root0Node2Step4Chunk7_2_checked, root0Node2Step4Chunk7_3_checked, root0Node2Step4Chunk7_4_checked, root0Node2Step4Chunk7_5_checked, root0Node2Step4Chunk8_0_checked, root0Node2Step4Chunk8_1_checked, root0Node2Step4Chunk8_2_checked, root0Node2Step4Chunk8_3_checked, root0Node2Step4Chunk8_4_checked, root0Node2Step4Chunk8_5_checked, Bool.true_and])
theorem root0Node2Step4_checked :
    checkReplacement table21 root0Node2Domains3 root0Node2Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root0Node2Domains3 root0Node2Domains4
    root0Node2Domains3Fast root0Node2Domains4Fast
    root0Node2Domains3_fast_eq root0Node2Domains4_fast_eq
    root0Node2Step4Narrowing_checked (by decide)
theorem root0Node2Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node2Domains4 (.output 0) = true := by decide
def root0Node3Domains0 : Domains 91 State := restrict root0Node1Domains4 5 (8,4)
def root0Node3Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(4,5),(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5),(6,5)]
  | 13 => some [(0,0),(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2),(1,5)]
  | 22 => some [(1,1),(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2),(5,5)]
  | 31 => some [(7,0),(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4),(0,5),(6,2)]
  | 41 => some [(4,4),(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(4,3),(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node3Domains0_fast_eq : root0Node3Domains0 = expandDomains root0Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node3Domains0 v = expandDomains root0Node3Domains0Fast v from by decide) v
def root0Node3Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(4,5),(8,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(0,0),(6,3)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2),(1,5)]
  | 22 => [(1,1),(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(5,2),(5,5)]
  | 31 => [(7,0),(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2)]
  | 40 => [(0,4),(0,5),(6,2)]
  | 41 => [(4,4),(5,4),(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(5,2)]
  | 50 => [(8,0)]
  | 51 => [(4,3),(7,1)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(0,4),(1,2),(6,2)]
  | 71 => [(5,4),(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3),(6,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(8,0)]
  | 78 => [(4,3),(7,1),(8,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1),(8,1)]
  | 82 => [(0,2),(6,5)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(0,5),(4,5),(5,5),(8,5)]
  | 86 => [(2,0),(7,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(8,5)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node3Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(4,5),(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(0,0),(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2),(1,5)]
  | 22 => some [(1,1),(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2),(5,5)]
  | 31 => some [(7,0),(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4),(0,5),(6,2)]
  | 41 => some [(4,4),(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(4,3),(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node3Domains1_fast_eq : root0Node3Domains1 = expandDomains root0Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node3Domains1 v = expandDomains root0Node3Domains1Fast v from by decide) v
theorem root0Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Narrowing_checked :
    checkNarrowing table36 root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root0Node3Domains0 root0Node3Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node3Step1Chunk0_0_checked, root0Node3Step1Chunk0_1_checked, root0Node3Step1Chunk0_2_checked, root0Node3Step1Chunk0_3_checked, root0Node3Step1Chunk0_4_checked, root0Node3Step1Chunk0_5_checked, root0Node3Step1Chunk1_0_checked, root0Node3Step1Chunk1_1_checked, root0Node3Step1Chunk1_2_checked, root0Node3Step1Chunk1_3_checked, root0Node3Step1Chunk1_4_checked, root0Node3Step1Chunk1_5_checked, root0Node3Step1Chunk2_0_checked, root0Node3Step1Chunk2_1_checked, root0Node3Step1Chunk2_2_checked, root0Node3Step1Chunk2_3_checked, root0Node3Step1Chunk2_4_checked, root0Node3Step1Chunk2_5_checked, root0Node3Step1Chunk3_0_checked, root0Node3Step1Chunk3_1_checked, root0Node3Step1Chunk3_2_checked, root0Node3Step1Chunk3_3_checked, root0Node3Step1Chunk3_4_checked, root0Node3Step1Chunk3_5_checked, root0Node3Step1Chunk4_0_checked, root0Node3Step1Chunk4_1_checked, root0Node3Step1Chunk4_2_checked, root0Node3Step1Chunk4_3_checked, root0Node3Step1Chunk4_4_checked, root0Node3Step1Chunk4_5_checked, root0Node3Step1Chunk5_0_checked, root0Node3Step1Chunk5_1_checked, root0Node3Step1Chunk5_2_checked, root0Node3Step1Chunk5_3_checked, root0Node3Step1Chunk5_4_checked, root0Node3Step1Chunk5_5_checked, root0Node3Step1Chunk6_0_checked, root0Node3Step1Chunk6_1_checked, root0Node3Step1Chunk6_2_checked, root0Node3Step1Chunk6_3_checked, root0Node3Step1Chunk6_4_checked, root0Node3Step1Chunk6_5_checked, root0Node3Step1Chunk7_0_checked, root0Node3Step1Chunk7_1_checked, root0Node3Step1Chunk7_2_checked, root0Node3Step1Chunk7_3_checked, root0Node3Step1Chunk7_4_checked, root0Node3Step1Chunk7_5_checked, root0Node3Step1Chunk8_0_checked, root0Node3Step1Chunk8_1_checked, root0Node3Step1Chunk8_2_checked, root0Node3Step1Chunk8_3_checked, root0Node3Step1Chunk8_4_checked, root0Node3Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node3Step1_checked :
    checkReplacement table36 root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq
    root0Node3Step1Narrowing_checked (by decide)
def root0Node4Domains0 : Domains 91 State := restrict root0Node3Domains1 6 (4,5)
def root0Node4Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(0,0),(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2),(1,5)]
  | 22 => some [(1,1),(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2),(5,5)]
  | 31 => some [(7,0),(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4),(0,5),(6,2)]
  | 41 => some [(4,4),(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(4,3),(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node4Domains0_fast_eq : root0Node4Domains0 = expandDomains root0Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node4Domains0 v = expandDomains root0Node4Domains0Fast v from by decide) v
def root0Node4Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(7,0)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(5,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(5,2)]
  | 50 => [(8,0)]
  | 51 => [(7,1)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(7,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(6,2)]
  | 71 => [(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(8,0)]
  | 78 => [(7,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(0,5),(4,5),(5,5),(8,5)]
  | 86 => [(2,0),(7,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(8,5)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node4Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node4Domains1_fast_eq : root0Node4Domains1 = expandDomains root0Node4Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node4Domains1 v = expandDomains root0Node4Domains1Fast v from by decide) v
theorem root0Node4Step1Chunk0_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_0⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk0_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_1⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk0_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_2⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk0_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_3⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk0_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_4⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk0_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_5⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk1_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_0⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk1_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_1⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk1_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_2⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk1_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_3⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk1_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_4⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk1_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_5⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk2_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_0⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk2_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_1⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk2_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_2⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk2_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_3⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk2_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_4⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk2_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_5⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk3_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_0⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk3_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_1⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk3_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_2⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk3_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_3⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk3_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_4⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk3_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_5⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk4_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_0⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk4_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_1⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk4_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_2⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk4_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_3⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk4_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_4⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk4_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_5⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk5_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_0⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk5_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_1⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk5_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_2⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk5_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_3⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk5_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_4⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk5_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_5⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk6_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_0⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk6_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_1⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk6_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_2⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk6_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_3⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk6_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_4⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk6_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_5⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk7_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_0⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk7_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_1⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk7_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_2⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk7_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_3⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk7_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_4⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk7_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_5⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk8_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_0⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk8_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_1⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk8_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_2⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk8_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_3⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk8_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_4⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Chunk8_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_5⟩
      root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq (by decide)
theorem root0Node4Step1Narrowing_checked :
    checkNarrowing table44 root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkNarrowing_flatten table44Scope [table44Rows0_0,table44Rows0_1,table44Rows0_2,table44Rows0_3,table44Rows0_4,table44Rows0_5,table44Rows1_0,table44Rows1_1,table44Rows1_2,table44Rows1_3,table44Rows1_4,table44Rows1_5,table44Rows2_0,table44Rows2_1,table44Rows2_2,table44Rows2_3,table44Rows2_4,table44Rows2_5,table44Rows3_0,table44Rows3_1,table44Rows3_2,table44Rows3_3,table44Rows3_4,table44Rows3_5,table44Rows4_0,table44Rows4_1,table44Rows4_2,table44Rows4_3,table44Rows4_4,table44Rows4_5,table44Rows5_0,table44Rows5_1,table44Rows5_2,table44Rows5_3,table44Rows5_4,table44Rows5_5,table44Rows6_0,table44Rows6_1,table44Rows6_2,table44Rows6_3,table44Rows6_4,table44Rows6_5,table44Rows7_0,table44Rows7_1,table44Rows7_2,table44Rows7_3,table44Rows7_4,table44Rows7_5,table44Rows8_0,table44Rows8_1,table44Rows8_2,table44Rows8_3,table44Rows8_4,table44Rows8_5]
    root0Node4Domains0 root0Node4Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node4Step1Chunk0_0_checked, root0Node4Step1Chunk0_1_checked, root0Node4Step1Chunk0_2_checked, root0Node4Step1Chunk0_3_checked, root0Node4Step1Chunk0_4_checked, root0Node4Step1Chunk0_5_checked, root0Node4Step1Chunk1_0_checked, root0Node4Step1Chunk1_1_checked, root0Node4Step1Chunk1_2_checked, root0Node4Step1Chunk1_3_checked, root0Node4Step1Chunk1_4_checked, root0Node4Step1Chunk1_5_checked, root0Node4Step1Chunk2_0_checked, root0Node4Step1Chunk2_1_checked, root0Node4Step1Chunk2_2_checked, root0Node4Step1Chunk2_3_checked, root0Node4Step1Chunk2_4_checked, root0Node4Step1Chunk2_5_checked, root0Node4Step1Chunk3_0_checked, root0Node4Step1Chunk3_1_checked, root0Node4Step1Chunk3_2_checked, root0Node4Step1Chunk3_3_checked, root0Node4Step1Chunk3_4_checked, root0Node4Step1Chunk3_5_checked, root0Node4Step1Chunk4_0_checked, root0Node4Step1Chunk4_1_checked, root0Node4Step1Chunk4_2_checked, root0Node4Step1Chunk4_3_checked, root0Node4Step1Chunk4_4_checked, root0Node4Step1Chunk4_5_checked, root0Node4Step1Chunk5_0_checked, root0Node4Step1Chunk5_1_checked, root0Node4Step1Chunk5_2_checked, root0Node4Step1Chunk5_3_checked, root0Node4Step1Chunk5_4_checked, root0Node4Step1Chunk5_5_checked, root0Node4Step1Chunk6_0_checked, root0Node4Step1Chunk6_1_checked, root0Node4Step1Chunk6_2_checked, root0Node4Step1Chunk6_3_checked, root0Node4Step1Chunk6_4_checked, root0Node4Step1Chunk6_5_checked, root0Node4Step1Chunk7_0_checked, root0Node4Step1Chunk7_1_checked, root0Node4Step1Chunk7_2_checked, root0Node4Step1Chunk7_3_checked, root0Node4Step1Chunk7_4_checked, root0Node4Step1Chunk7_5_checked, root0Node4Step1Chunk8_0_checked, root0Node4Step1Chunk8_1_checked, root0Node4Step1Chunk8_2_checked, root0Node4Step1Chunk8_3_checked, root0Node4Step1Chunk8_4_checked, root0Node4Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node4Step1_checked :
    checkReplacement table44 root0Node4Domains0 root0Node4Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node4Domains0 root0Node4Domains1
    root0Node4Domains0Fast root0Node4Domains1Fast
    root0Node4Domains0_fast_eq root0Node4Domains1_fast_eq
    root0Node4Step1Narrowing_checked (by decide)
def root0Node4Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(7,0)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(5,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(5,2)]
  | 50 => [(8,0)]
  | 51 => [(7,1)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(7,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(6,2)]
  | 71 => [(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(8,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(4,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(8,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root0Node4Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(8,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(4,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(8,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root0Node4Domains2_fast_eq : root0Node4Domains2 = expandDomains root0Node4Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node4Domains2 v = expandDomains root0Node4Domains2Fast v from by decide) v
theorem root0Node4Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq (by decide)
theorem root0Node4Step2Narrowing_checked :
    checkNarrowing table65 root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root0Node4Domains1 root0Node4Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node4Step2Chunk0_0_checked, root0Node4Step2Chunk0_1_checked, root0Node4Step2Chunk0_2_checked, root0Node4Step2Chunk0_3_checked, root0Node4Step2Chunk0_4_checked, root0Node4Step2Chunk0_5_checked, root0Node4Step2Chunk1_0_checked, root0Node4Step2Chunk1_1_checked, root0Node4Step2Chunk1_2_checked, root0Node4Step2Chunk1_3_checked, root0Node4Step2Chunk1_4_checked, root0Node4Step2Chunk1_5_checked, root0Node4Step2Chunk2_0_checked, root0Node4Step2Chunk2_1_checked, root0Node4Step2Chunk2_2_checked, root0Node4Step2Chunk2_3_checked, root0Node4Step2Chunk2_4_checked, root0Node4Step2Chunk2_5_checked, root0Node4Step2Chunk3_0_checked, root0Node4Step2Chunk3_1_checked, root0Node4Step2Chunk3_2_checked, root0Node4Step2Chunk3_3_checked, root0Node4Step2Chunk3_4_checked, root0Node4Step2Chunk3_5_checked, root0Node4Step2Chunk4_0_checked, root0Node4Step2Chunk4_1_checked, root0Node4Step2Chunk4_2_checked, root0Node4Step2Chunk4_3_checked, root0Node4Step2Chunk4_4_checked, root0Node4Step2Chunk4_5_checked, root0Node4Step2Chunk5_0_checked, root0Node4Step2Chunk5_1_checked, root0Node4Step2Chunk5_2_checked, root0Node4Step2Chunk5_3_checked, root0Node4Step2Chunk5_4_checked, root0Node4Step2Chunk5_5_checked, root0Node4Step2Chunk6_0_checked, root0Node4Step2Chunk6_1_checked, root0Node4Step2Chunk6_2_checked, root0Node4Step2Chunk6_3_checked, root0Node4Step2Chunk6_4_checked, root0Node4Step2Chunk6_5_checked, root0Node4Step2Chunk7_0_checked, root0Node4Step2Chunk7_1_checked, root0Node4Step2Chunk7_2_checked, root0Node4Step2Chunk7_3_checked, root0Node4Step2Chunk7_4_checked, root0Node4Step2Chunk7_5_checked, root0Node4Step2Chunk8_0_checked, root0Node4Step2Chunk8_1_checked, root0Node4Step2Chunk8_2_checked, root0Node4Step2Chunk8_3_checked, root0Node4Step2Chunk8_4_checked, root0Node4Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node4Step2_checked :
    checkReplacement table65 root0Node4Domains1 root0Node4Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node4Domains1 root0Node4Domains2
    root0Node4Domains1Fast root0Node4Domains2Fast
    root0Node4Domains1_fast_eq root0Node4Domains2_fast_eq
    root0Node4Step2Narrowing_checked (by decide)
theorem root0Node4Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node4Domains2 (.output 1) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
