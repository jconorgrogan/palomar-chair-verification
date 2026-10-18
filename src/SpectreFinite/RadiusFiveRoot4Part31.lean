module

public import SpectreFinite.RadiusFiveRoot4Part30
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable4
public import SpectreFinite.RadiusFiveTable40
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node78Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(7,5)]
  | 22 => [(6,0)]
  | 23 => [(3,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(7,3)]
  | 31 => [(8,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0)]
  | 76 => [(3,2)]
  | 77 => [(4,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node78Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(7,5)]
  | 22 => some [(6,0)]
  | 23 => some [(3,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(8,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node78Domains3_fast_eq : root4Node78Domains3 = expandDomains root4Node78Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node78Domains3 v = expandDomains root4Node78Domains3Fast v from by decide) v
theorem root4Node78Step3Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq (by decide)
theorem root4Node78Step3Narrowing_checked :
    checkNarrowing table12 root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root4Node78Domains2 root4Node78Domains3 (by
      simp only [List.all_cons, List.all_nil, root4Node78Step3Chunk0_0_checked, root4Node78Step3Chunk0_1_checked, root4Node78Step3Chunk0_2_checked, root4Node78Step3Chunk0_3_checked, root4Node78Step3Chunk0_4_checked, root4Node78Step3Chunk0_5_checked, root4Node78Step3Chunk1_0_checked, root4Node78Step3Chunk1_1_checked, root4Node78Step3Chunk1_2_checked, root4Node78Step3Chunk1_3_checked, root4Node78Step3Chunk1_4_checked, root4Node78Step3Chunk1_5_checked, root4Node78Step3Chunk2_0_checked, root4Node78Step3Chunk2_1_checked, root4Node78Step3Chunk2_2_checked, root4Node78Step3Chunk2_3_checked, root4Node78Step3Chunk2_4_checked, root4Node78Step3Chunk2_5_checked, root4Node78Step3Chunk3_0_checked, root4Node78Step3Chunk3_1_checked, root4Node78Step3Chunk3_2_checked, root4Node78Step3Chunk3_3_checked, root4Node78Step3Chunk3_4_checked, root4Node78Step3Chunk3_5_checked, root4Node78Step3Chunk4_0_checked, root4Node78Step3Chunk4_1_checked, root4Node78Step3Chunk4_2_checked, root4Node78Step3Chunk4_3_checked, root4Node78Step3Chunk4_4_checked, root4Node78Step3Chunk4_5_checked, root4Node78Step3Chunk5_0_checked, root4Node78Step3Chunk5_1_checked, root4Node78Step3Chunk5_2_checked, root4Node78Step3Chunk5_3_checked, root4Node78Step3Chunk5_4_checked, root4Node78Step3Chunk5_5_checked, root4Node78Step3Chunk6_0_checked, root4Node78Step3Chunk6_1_checked, root4Node78Step3Chunk6_2_checked, root4Node78Step3Chunk6_3_checked, root4Node78Step3Chunk6_4_checked, root4Node78Step3Chunk6_5_checked, root4Node78Step3Chunk7_0_checked, root4Node78Step3Chunk7_1_checked, root4Node78Step3Chunk7_2_checked, root4Node78Step3Chunk7_3_checked, root4Node78Step3Chunk7_4_checked, root4Node78Step3Chunk7_5_checked, root4Node78Step3Chunk8_0_checked, root4Node78Step3Chunk8_1_checked, root4Node78Step3Chunk8_2_checked, root4Node78Step3Chunk8_3_checked, root4Node78Step3Chunk8_4_checked, root4Node78Step3Chunk8_5_checked, Bool.true_and])
theorem root4Node78Step3_checked :
    checkReplacement table12 root4Node78Domains2 root4Node78Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root4Node78Domains2 root4Node78Domains3
    root4Node78Domains2Fast root4Node78Domains3Fast
    root4Node78Domains2_fast_eq root4Node78Domains3_fast_eq
    root4Node78Step3Narrowing_checked (by decide)
theorem root4Node78Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node78Domains3 (.output 38) = true := by decide
def root4Node79Domains0 : Domains 91 State := restrict root4Node77Domains2 19 (8,3)
def root4Node79Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(7,5)]
  | 22 => some [(6,0)]
  | 23 => some [(3,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(8,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(7,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(4,2),(7,0)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,1)]
  | 70 => some [(0,0),(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0)]
  | 78 => some [(1,1),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node79Domains0_fast_eq : root4Node79Domains0 = expandDomains root4Node79Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node79Domains0 v = expandDomains root4Node79Domains0Fast v from by decide) v
def root4Node79Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1),(5,1),(8,1)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(7,5)]
  | 22 => [(6,0)]
  | 23 => [(3,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4),(8,4)]
  | 30 => [(7,3)]
  | 31 => [(8,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(1,5),(7,5)]
  | 40 => [(0,1),(6,4)]
  | 41 => [(1,2),(6,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0),(8,0)]
  | 49 => [(4,5),(7,3)]
  | 50 => [(4,2),(7,0)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(5,0),(5,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,1)]
  | 70 => [(0,0),(0,5),(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3),(6,3)]
  | 74 => [(7,2),(8,2)]
  | 75 => [(4,0),(5,0),(8,0)]
  | 76 => [(4,5),(7,3)]
  | 77 => [(4,2),(7,0)]
  | 78 => [(1,1),(6,1),(7,1)]
  | 79 => [(4,1),(8,1)]
  | 80 => [(0,2),(6,5)]
  | 81 => [(0,4),(1,1)]
  | 82 => [(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,4)]
  | 84 => [(1,2),(6,2),(7,2)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(5,5)]
  | 87 => [(7,0),(8,0)]
  | 88 => [(4,3),(8,3)]
  | 89 => [(1,5),(3,5),(5,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root4Node79Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(7,5)]
  | 22 => some [(6,0)]
  | 23 => some [(3,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(8,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5),(7,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0),(8,0)]
  | 49 => some [(4,5),(7,3)]
  | 50 => some [(4,2),(7,0)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(0,5),(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(1,1),(6,1),(7,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,4)]
  | 84 => some [(1,2),(6,2),(7,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root4Node79Domains1_fast_eq : root4Node79Domains1 = expandDomains root4Node79Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node79Domains1 v = expandDomains root4Node79Domains1Fast v from by decide) v
theorem root4Node79Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq (by decide)
theorem root4Node79Step1Narrowing_checked :
    checkNarrowing table56 root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root4Node79Domains0 root4Node79Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node79Step1Chunk0_0_checked, root4Node79Step1Chunk0_1_checked, root4Node79Step1Chunk0_2_checked, root4Node79Step1Chunk0_3_checked, root4Node79Step1Chunk0_4_checked, root4Node79Step1Chunk0_5_checked, root4Node79Step1Chunk1_0_checked, root4Node79Step1Chunk1_1_checked, root4Node79Step1Chunk1_2_checked, root4Node79Step1Chunk1_3_checked, root4Node79Step1Chunk1_4_checked, root4Node79Step1Chunk1_5_checked, root4Node79Step1Chunk2_0_checked, root4Node79Step1Chunk2_1_checked, root4Node79Step1Chunk2_2_checked, root4Node79Step1Chunk2_3_checked, root4Node79Step1Chunk2_4_checked, root4Node79Step1Chunk2_5_checked, root4Node79Step1Chunk3_0_checked, root4Node79Step1Chunk3_1_checked, root4Node79Step1Chunk3_2_checked, root4Node79Step1Chunk3_3_checked, root4Node79Step1Chunk3_4_checked, root4Node79Step1Chunk3_5_checked, root4Node79Step1Chunk4_0_checked, root4Node79Step1Chunk4_1_checked, root4Node79Step1Chunk4_2_checked, root4Node79Step1Chunk4_3_checked, root4Node79Step1Chunk4_4_checked, root4Node79Step1Chunk4_5_checked, root4Node79Step1Chunk5_0_checked, root4Node79Step1Chunk5_1_checked, root4Node79Step1Chunk5_2_checked, root4Node79Step1Chunk5_3_checked, root4Node79Step1Chunk5_4_checked, root4Node79Step1Chunk5_5_checked, root4Node79Step1Chunk6_0_checked, root4Node79Step1Chunk6_1_checked, root4Node79Step1Chunk6_2_checked, root4Node79Step1Chunk6_3_checked, root4Node79Step1Chunk6_4_checked, root4Node79Step1Chunk6_5_checked, root4Node79Step1Chunk7_0_checked, root4Node79Step1Chunk7_1_checked, root4Node79Step1Chunk7_2_checked, root4Node79Step1Chunk7_3_checked, root4Node79Step1Chunk7_4_checked, root4Node79Step1Chunk7_5_checked, root4Node79Step1Chunk8_0_checked, root4Node79Step1Chunk8_1_checked, root4Node79Step1Chunk8_2_checked, root4Node79Step1Chunk8_3_checked, root4Node79Step1Chunk8_4_checked, root4Node79Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node79Step1_checked :
    checkReplacement table56 root4Node79Domains0 root4Node79Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node79Domains0 root4Node79Domains1
    root4Node79Domains0Fast root4Node79Domains1Fast
    root4Node79Domains0_fast_eq root4Node79Domains1_fast_eq
    root4Node79Step1Narrowing_checked (by decide)
def root4Node79Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(5,1),(8,1)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(7,5)]
  | 22 => [(6,0)]
  | 23 => [(3,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(7,3)]
  | 31 => [(8,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(1,5),(7,5)]
  | 40 => [(0,1),(6,4)]
  | 41 => [(1,2),(6,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0),(8,0)]
  | 49 => [(4,5),(7,3)]
  | 50 => [(4,2),(7,0)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(5,0),(5,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,1)]
  | 70 => [(0,0),(0,5),(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3),(6,3)]
  | 74 => [(7,2),(8,2)]
  | 75 => [(4,0),(5,0),(8,0)]
  | 76 => [(4,5),(7,3)]
  | 77 => [(4,2),(7,0)]
  | 78 => [(1,1),(6,1),(7,1)]
  | 79 => [(4,1),(8,1)]
  | 80 => [(0,2),(6,5)]
  | 81 => [(0,4),(1,1)]
  | 82 => [(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,4)]
  | 84 => [(1,2),(6,2),(7,2)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(5,5)]
  | 87 => [(7,0),(8,0)]
  | 88 => [(4,3),(8,3)]
  | 89 => [(1,5),(3,5),(5,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root4Node79Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(5,1),(8,1)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(7,5)]
  | 22 => some [(6,0)]
  | 23 => some [(3,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(8,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5),(7,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0),(8,0)]
  | 49 => some [(4,5),(7,3)]
  | 50 => some [(4,2),(7,0)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(0,5),(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(1,1),(6,1),(7,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,4)]
  | 84 => some [(1,2),(6,2),(7,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root4Node79Domains2_fast_eq : root4Node79Domains2 = expandDomains root4Node79Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node79Domains2 v = expandDomains root4Node79Domains2Fast v from by decide) v
theorem root4Node79Step2Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq (by decide)
theorem root4Node79Step2Narrowing_checked :
    checkNarrowing table4 root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkNarrowing_flatten table4Scope [table4Rows0_0,table4Rows0_1,table4Rows0_2,table4Rows0_3,table4Rows0_4,table4Rows0_5,table4Rows1_0,table4Rows1_1,table4Rows1_2,table4Rows1_3,table4Rows1_4,table4Rows1_5,table4Rows2_0,table4Rows2_1,table4Rows2_2,table4Rows2_3,table4Rows2_4,table4Rows2_5,table4Rows3_0,table4Rows3_1,table4Rows3_2,table4Rows3_3,table4Rows3_4,table4Rows3_5,table4Rows4_0,table4Rows4_1,table4Rows4_2,table4Rows4_3,table4Rows4_4,table4Rows4_5,table4Rows5_0,table4Rows5_1,table4Rows5_2,table4Rows5_3,table4Rows5_4,table4Rows5_5,table4Rows6_0,table4Rows6_1,table4Rows6_2,table4Rows6_3,table4Rows6_4,table4Rows6_5,table4Rows7_0,table4Rows7_1,table4Rows7_2,table4Rows7_3,table4Rows7_4,table4Rows7_5,table4Rows8_0,table4Rows8_1,table4Rows8_2,table4Rows8_3,table4Rows8_4,table4Rows8_5]
    root4Node79Domains1 root4Node79Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node79Step2Chunk0_0_checked, root4Node79Step2Chunk0_1_checked, root4Node79Step2Chunk0_2_checked, root4Node79Step2Chunk0_3_checked, root4Node79Step2Chunk0_4_checked, root4Node79Step2Chunk0_5_checked, root4Node79Step2Chunk1_0_checked, root4Node79Step2Chunk1_1_checked, root4Node79Step2Chunk1_2_checked, root4Node79Step2Chunk1_3_checked, root4Node79Step2Chunk1_4_checked, root4Node79Step2Chunk1_5_checked, root4Node79Step2Chunk2_0_checked, root4Node79Step2Chunk2_1_checked, root4Node79Step2Chunk2_2_checked, root4Node79Step2Chunk2_3_checked, root4Node79Step2Chunk2_4_checked, root4Node79Step2Chunk2_5_checked, root4Node79Step2Chunk3_0_checked, root4Node79Step2Chunk3_1_checked, root4Node79Step2Chunk3_2_checked, root4Node79Step2Chunk3_3_checked, root4Node79Step2Chunk3_4_checked, root4Node79Step2Chunk3_5_checked, root4Node79Step2Chunk4_0_checked, root4Node79Step2Chunk4_1_checked, root4Node79Step2Chunk4_2_checked, root4Node79Step2Chunk4_3_checked, root4Node79Step2Chunk4_4_checked, root4Node79Step2Chunk4_5_checked, root4Node79Step2Chunk5_0_checked, root4Node79Step2Chunk5_1_checked, root4Node79Step2Chunk5_2_checked, root4Node79Step2Chunk5_3_checked, root4Node79Step2Chunk5_4_checked, root4Node79Step2Chunk5_5_checked, root4Node79Step2Chunk6_0_checked, root4Node79Step2Chunk6_1_checked, root4Node79Step2Chunk6_2_checked, root4Node79Step2Chunk6_3_checked, root4Node79Step2Chunk6_4_checked, root4Node79Step2Chunk6_5_checked, root4Node79Step2Chunk7_0_checked, root4Node79Step2Chunk7_1_checked, root4Node79Step2Chunk7_2_checked, root4Node79Step2Chunk7_3_checked, root4Node79Step2Chunk7_4_checked, root4Node79Step2Chunk7_5_checked, root4Node79Step2Chunk8_0_checked, root4Node79Step2Chunk8_1_checked, root4Node79Step2Chunk8_2_checked, root4Node79Step2Chunk8_3_checked, root4Node79Step2Chunk8_4_checked, root4Node79Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node79Step2_checked :
    checkReplacement table4 root4Node79Domains1 root4Node79Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node79Domains1 root4Node79Domains2
    root4Node79Domains1Fast root4Node79Domains2Fast
    root4Node79Domains1_fast_eq root4Node79Domains2_fast_eq
    root4Node79Step2Narrowing_checked (by decide)
def root4Node79Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(5,1),(8,1)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(7,5)]
  | 22 => [(6,0)]
  | 23 => [(3,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(7,3)]
  | 31 => [(8,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(1,5),(7,5)]
  | 40 => [(0,1),(6,4)]
  | 41 => [(1,2),(6,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0),(8,0)]
  | 49 => [(4,5),(7,3)]
  | 50 => [(4,2),(7,0)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(5,0),(5,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,1)]
  | 70 => [(0,0),(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3),(6,3)]
  | 74 => [(7,2),(8,2)]
  | 75 => [(4,0),(5,0),(8,0)]
  | 76 => [(4,5),(7,3)]
  | 77 => [(4,2),(7,0)]
  | 78 => [(1,1),(6,1)]
  | 79 => [(4,1),(8,1)]
  | 80 => [(0,2),(6,5)]
  | 81 => [(0,4),(1,1)]
  | 82 => [(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,4)]
  | 84 => [(1,2),(6,2),(7,2)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(5,5)]
  | 87 => [(7,0),(8,0)]
  | 88 => [(4,3),(8,3)]
  | 89 => [(1,5),(3,5),(5,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root4Node79Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(5,1),(8,1)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(7,5)]
  | 22 => some [(6,0)]
  | 23 => some [(3,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(8,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5),(7,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0),(8,0)]
  | 49 => some [(4,5),(7,3)]
  | 50 => some [(4,2),(7,0)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(1,1),(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,4)]
  | 84 => some [(1,2),(6,2),(7,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root4Node79Domains3_fast_eq : root4Node79Domains3 = expandDomains root4Node79Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node79Domains3 v = expandDomains root4Node79Domains3Fast v from by decide) v
theorem root4Node79Step3Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq (by decide)
theorem root4Node79Step3Narrowing_checked :
    checkNarrowing table40 root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkNarrowing_flatten table40Scope [table40Rows0_0,table40Rows0_1,table40Rows0_2,table40Rows0_3,table40Rows0_4,table40Rows0_5,table40Rows1_0,table40Rows1_1,table40Rows1_2,table40Rows1_3,table40Rows1_4,table40Rows1_5,table40Rows2_0,table40Rows2_1,table40Rows2_2,table40Rows2_3,table40Rows2_4,table40Rows2_5,table40Rows3_0,table40Rows3_1,table40Rows3_2,table40Rows3_3,table40Rows3_4,table40Rows3_5,table40Rows4_0,table40Rows4_1,table40Rows4_2,table40Rows4_3,table40Rows4_4,table40Rows4_5,table40Rows5_0,table40Rows5_1,table40Rows5_2,table40Rows5_3,table40Rows5_4,table40Rows5_5,table40Rows6_0,table40Rows6_1,table40Rows6_2,table40Rows6_3,table40Rows6_4,table40Rows6_5,table40Rows7_0,table40Rows7_1,table40Rows7_2,table40Rows7_3,table40Rows7_4,table40Rows7_5,table40Rows8_0,table40Rows8_1,table40Rows8_2,table40Rows8_3,table40Rows8_4,table40Rows8_5]
    root4Node79Domains2 root4Node79Domains3 (by
      simp only [List.all_cons, List.all_nil, root4Node79Step3Chunk0_0_checked, root4Node79Step3Chunk0_1_checked, root4Node79Step3Chunk0_2_checked, root4Node79Step3Chunk0_3_checked, root4Node79Step3Chunk0_4_checked, root4Node79Step3Chunk0_5_checked, root4Node79Step3Chunk1_0_checked, root4Node79Step3Chunk1_1_checked, root4Node79Step3Chunk1_2_checked, root4Node79Step3Chunk1_3_checked, root4Node79Step3Chunk1_4_checked, root4Node79Step3Chunk1_5_checked, root4Node79Step3Chunk2_0_checked, root4Node79Step3Chunk2_1_checked, root4Node79Step3Chunk2_2_checked, root4Node79Step3Chunk2_3_checked, root4Node79Step3Chunk2_4_checked, root4Node79Step3Chunk2_5_checked, root4Node79Step3Chunk3_0_checked, root4Node79Step3Chunk3_1_checked, root4Node79Step3Chunk3_2_checked, root4Node79Step3Chunk3_3_checked, root4Node79Step3Chunk3_4_checked, root4Node79Step3Chunk3_5_checked, root4Node79Step3Chunk4_0_checked, root4Node79Step3Chunk4_1_checked, root4Node79Step3Chunk4_2_checked, root4Node79Step3Chunk4_3_checked, root4Node79Step3Chunk4_4_checked, root4Node79Step3Chunk4_5_checked, root4Node79Step3Chunk5_0_checked, root4Node79Step3Chunk5_1_checked, root4Node79Step3Chunk5_2_checked, root4Node79Step3Chunk5_3_checked, root4Node79Step3Chunk5_4_checked, root4Node79Step3Chunk5_5_checked, root4Node79Step3Chunk6_0_checked, root4Node79Step3Chunk6_1_checked, root4Node79Step3Chunk6_2_checked, root4Node79Step3Chunk6_3_checked, root4Node79Step3Chunk6_4_checked, root4Node79Step3Chunk6_5_checked, root4Node79Step3Chunk7_0_checked, root4Node79Step3Chunk7_1_checked, root4Node79Step3Chunk7_2_checked, root4Node79Step3Chunk7_3_checked, root4Node79Step3Chunk7_4_checked, root4Node79Step3Chunk7_5_checked, root4Node79Step3Chunk8_0_checked, root4Node79Step3Chunk8_1_checked, root4Node79Step3Chunk8_2_checked, root4Node79Step3Chunk8_3_checked, root4Node79Step3Chunk8_4_checked, root4Node79Step3Chunk8_5_checked, Bool.true_and])
theorem root4Node79Step3_checked :
    checkReplacement table40 root4Node79Domains2 root4Node79Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root4Node79Domains2 root4Node79Domains3
    root4Node79Domains2Fast root4Node79Domains3Fast
    root4Node79Domains2_fast_eq root4Node79Domains3_fast_eq
    root4Node79Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
