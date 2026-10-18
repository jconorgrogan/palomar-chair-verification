module

public import SpectreFinite.RadiusFourRoot4Part18
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node52Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0),(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(4,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,2)]
  | 44 => [(8,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1)]
  | 49 => [(0,2)]
  | 50 => [(8,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(3,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(7,1)]
  | 59 => [(1,5)]
  | _ => [(6,1)]
def root4Node52Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0),(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(4,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,2)]
  | 44 => some [(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1)]
  | 49 => some [(0,2)]
  | 50 => some [(8,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(3,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(7,1)]
  | 59 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node52Domains4_fast_eq : root4Node52Domains4 = expandDomains root4Node52Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node52Domains4 v = expandDomains root4Node52Domains4Fast v from by decide) v
theorem root4Node52Step4Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root4Node52Domains3 root4Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node52Domains3 root4Node52Domains4
    root4Node52Domains3Fast root4Node52Domains4Fast
    root4Node52Domains3_fast_eq root4Node52Domains4_fast_eq (by decide)
theorem root4Node52Step4_checked :
    checkReplacement table2 root4Node52Domains3 root4Node52Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node52Step4Chunk0_0_checked, root4Node52Step4Chunk0_1_checked, root4Node52Step4Chunk0_2_checked, root4Node52Step4Chunk0_3_checked, root4Node52Step4Chunk0_4_checked, root4Node52Step4Chunk0_5_checked, root4Node52Step4Chunk1_0_checked, root4Node52Step4Chunk1_1_checked, root4Node52Step4Chunk1_2_checked, root4Node52Step4Chunk1_3_checked, root4Node52Step4Chunk1_4_checked, root4Node52Step4Chunk1_5_checked, root4Node52Step4Chunk2_0_checked, root4Node52Step4Chunk2_1_checked, root4Node52Step4Chunk2_2_checked, root4Node52Step4Chunk2_3_checked, root4Node52Step4Chunk2_4_checked, root4Node52Step4Chunk2_5_checked, root4Node52Step4Chunk3_0_checked, root4Node52Step4Chunk3_1_checked, root4Node52Step4Chunk3_2_checked, root4Node52Step4Chunk3_3_checked, root4Node52Step4Chunk3_4_checked, root4Node52Step4Chunk3_5_checked, root4Node52Step4Chunk4_0_checked, root4Node52Step4Chunk4_1_checked, root4Node52Step4Chunk4_2_checked, root4Node52Step4Chunk4_3_checked, root4Node52Step4Chunk4_4_checked, root4Node52Step4Chunk4_5_checked, root4Node52Step4Chunk5_0_checked, root4Node52Step4Chunk5_1_checked, root4Node52Step4Chunk5_2_checked, root4Node52Step4Chunk5_3_checked, root4Node52Step4Chunk5_4_checked, root4Node52Step4Chunk5_5_checked, root4Node52Step4Chunk6_0_checked, root4Node52Step4Chunk6_1_checked, root4Node52Step4Chunk6_2_checked, root4Node52Step4Chunk6_3_checked, root4Node52Step4Chunk6_4_checked, root4Node52Step4Chunk6_5_checked, root4Node52Step4Chunk7_0_checked, root4Node52Step4Chunk7_1_checked, root4Node52Step4Chunk7_2_checked, root4Node52Step4Chunk7_3_checked, root4Node52Step4Chunk7_4_checked, root4Node52Step4Chunk7_5_checked, root4Node52Step4Chunk8_0_checked, root4Node52Step4Chunk8_1_checked, root4Node52Step4Chunk8_2_checked, root4Node52Step4Chunk8_3_checked, root4Node52Step4Chunk8_4_checked, root4Node52Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node53Domains0 : Domains 61 State := restrict root4Node52Domains4 0 (1,0)
def root4Node53Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(4,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,2)]
  | 44 => some [(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1)]
  | 49 => some [(0,2)]
  | 50 => some [(8,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(3,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(7,1)]
  | 59 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node53Domains0_fast_eq : root4Node53Domains0 = expandDomains root4Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node53Domains0 v = expandDomains root4Node53Domains0Fast v from by decide) v
theorem root4Node53Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node53Domains0 (.output 26) = true := by decide
def root4Node54Domains0 : Domains 61 State := restrict root4Node52Domains4 0 (6,0)
def root4Node54Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(4,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,2)]
  | 44 => some [(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1)]
  | 49 => some [(0,2)]
  | 50 => some [(8,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(3,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(7,1)]
  | 59 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node54Domains0_fast_eq : root4Node54Domains0 = expandDomains root4Node54Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node54Domains0 v = expandDomains root4Node54Domains0Fast v from by decide) v
theorem root4Node54Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node54Domains0 (.output 27) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
