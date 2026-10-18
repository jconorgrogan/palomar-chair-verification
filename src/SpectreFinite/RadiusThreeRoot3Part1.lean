module

public import SpectreFinite.RadiusThreeRoot3Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root3Node0Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => [(7,1)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root3Node0Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(7,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root3Node0Domains4_fast_eq : root3Node0Domains4 = expandDomains root3Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root3Node0Domains4 v = expandDomains root3Node0Domains4Fast v from by decide) v
theorem root3Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root3Node0Domains3 root3Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root3Node0Domains3 root3Node0Domains4
    root3Node0Domains3Fast root3Node0Domains4Fast
    root3Node0Domains3_fast_eq root3Node0Domains4_fast_eq (by decide)
theorem root3Node0Step4_checked :
    checkReplacement table4 root3Node0Domains3 root3Node0Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node0Step4Chunk0_0_checked, root3Node0Step4Chunk0_1_checked, root3Node0Step4Chunk0_2_checked, root3Node0Step4Chunk0_3_checked, root3Node0Step4Chunk0_4_checked, root3Node0Step4Chunk0_5_checked, root3Node0Step4Chunk1_0_checked, root3Node0Step4Chunk1_1_checked, root3Node0Step4Chunk1_2_checked, root3Node0Step4Chunk1_3_checked, root3Node0Step4Chunk1_4_checked, root3Node0Step4Chunk1_5_checked, root3Node0Step4Chunk2_0_checked, root3Node0Step4Chunk2_1_checked, root3Node0Step4Chunk2_2_checked, root3Node0Step4Chunk2_3_checked, root3Node0Step4Chunk2_4_checked, root3Node0Step4Chunk2_5_checked, root3Node0Step4Chunk3_0_checked, root3Node0Step4Chunk3_1_checked, root3Node0Step4Chunk3_2_checked, root3Node0Step4Chunk3_3_checked, root3Node0Step4Chunk3_4_checked, root3Node0Step4Chunk3_5_checked, root3Node0Step4Chunk4_0_checked, root3Node0Step4Chunk4_1_checked, root3Node0Step4Chunk4_2_checked, root3Node0Step4Chunk4_3_checked, root3Node0Step4Chunk4_4_checked, root3Node0Step4Chunk4_5_checked, root3Node0Step4Chunk5_0_checked, root3Node0Step4Chunk5_1_checked, root3Node0Step4Chunk5_2_checked, root3Node0Step4Chunk5_3_checked, root3Node0Step4Chunk5_4_checked, root3Node0Step4Chunk5_5_checked, root3Node0Step4Chunk6_0_checked, root3Node0Step4Chunk6_1_checked, root3Node0Step4Chunk6_2_checked, root3Node0Step4Chunk6_3_checked, root3Node0Step4Chunk6_4_checked, root3Node0Step4Chunk6_5_checked, root3Node0Step4Chunk7_0_checked, root3Node0Step4Chunk7_1_checked, root3Node0Step4Chunk7_2_checked, root3Node0Step4Chunk7_3_checked, root3Node0Step4Chunk7_4_checked, root3Node0Step4Chunk7_5_checked, root3Node0Step4Chunk8_0_checked, root3Node0Step4Chunk8_1_checked, root3Node0Step4Chunk8_2_checked, root3Node0Step4Chunk8_3_checked, root3Node0Step4Chunk8_4_checked, root3Node0Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root3Node1Domains0 : Domains 37 State := restrict root3Node0Domains4 9 (1,1)
def root3Node1Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(1,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(7,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root3Node1Domains0_fast_eq : root3Node1Domains0 = expandDomains root3Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root3Node1Domains0 v = expandDomains root3Node1Domains0Fast v from by decide) v
def root3Node1Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => [(1,1)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => [(7,1)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root3Node1Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(1,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(7,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root3Node1Domains1_fast_eq : root3Node1Domains1 = expandDomains root3Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root3Node1Domains1 v = expandDomains root3Node1Domains1Fast v from by decide) v
theorem root3Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root3Node1Domains0 root3Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node1Domains0 root3Node1Domains1
    root3Node1Domains0Fast root3Node1Domains1Fast
    root3Node1Domains0_fast_eq root3Node1Domains1_fast_eq (by decide)
theorem root3Node1Step1_checked :
    checkReplacement table4 root3Node1Domains0 root3Node1Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node1Step1Chunk0_0_checked, root3Node1Step1Chunk0_1_checked, root3Node1Step1Chunk0_2_checked, root3Node1Step1Chunk0_3_checked, root3Node1Step1Chunk0_4_checked, root3Node1Step1Chunk0_5_checked, root3Node1Step1Chunk1_0_checked, root3Node1Step1Chunk1_1_checked, root3Node1Step1Chunk1_2_checked, root3Node1Step1Chunk1_3_checked, root3Node1Step1Chunk1_4_checked, root3Node1Step1Chunk1_5_checked, root3Node1Step1Chunk2_0_checked, root3Node1Step1Chunk2_1_checked, root3Node1Step1Chunk2_2_checked, root3Node1Step1Chunk2_3_checked, root3Node1Step1Chunk2_4_checked, root3Node1Step1Chunk2_5_checked, root3Node1Step1Chunk3_0_checked, root3Node1Step1Chunk3_1_checked, root3Node1Step1Chunk3_2_checked, root3Node1Step1Chunk3_3_checked, root3Node1Step1Chunk3_4_checked, root3Node1Step1Chunk3_5_checked, root3Node1Step1Chunk4_0_checked, root3Node1Step1Chunk4_1_checked, root3Node1Step1Chunk4_2_checked, root3Node1Step1Chunk4_3_checked, root3Node1Step1Chunk4_4_checked, root3Node1Step1Chunk4_5_checked, root3Node1Step1Chunk5_0_checked, root3Node1Step1Chunk5_1_checked, root3Node1Step1Chunk5_2_checked, root3Node1Step1Chunk5_3_checked, root3Node1Step1Chunk5_4_checked, root3Node1Step1Chunk5_5_checked, root3Node1Step1Chunk6_0_checked, root3Node1Step1Chunk6_1_checked, root3Node1Step1Chunk6_2_checked, root3Node1Step1Chunk6_3_checked, root3Node1Step1Chunk6_4_checked, root3Node1Step1Chunk6_5_checked, root3Node1Step1Chunk7_0_checked, root3Node1Step1Chunk7_1_checked, root3Node1Step1Chunk7_2_checked, root3Node1Step1Chunk7_3_checked, root3Node1Step1Chunk7_4_checked, root3Node1Step1Chunk7_5_checked, root3Node1Step1Chunk8_0_checked, root3Node1Step1Chunk8_1_checked, root3Node1Step1Chunk8_2_checked, root3Node1Step1Chunk8_3_checked, root3Node1Step1Chunk8_4_checked, root3Node1Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root3Node1Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node1Domains1 (.output 0) = true := by decide
def root3Node2Domains0 : Domains 37 State := restrict root3Node0Domains4 9 (6,1)
def root3Node2Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(7,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root3Node2Domains0_fast_eq : root3Node2Domains0 = expandDomains root3Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root3Node2Domains0 v = expandDomains root3Node2Domains0Fast v from by decide) v
def root3Node2Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => [(6,1)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => [(7,1)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root3Node2Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(7,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root3Node2Domains1_fast_eq : root3Node2Domains1 = expandDomains root3Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root3Node2Domains1 v = expandDomains root3Node2Domains1Fast v from by decide) v
theorem root3Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root3Node2Domains0 root3Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node2Domains0 root3Node2Domains1
    root3Node2Domains0Fast root3Node2Domains1Fast
    root3Node2Domains0_fast_eq root3Node2Domains1_fast_eq (by decide)
theorem root3Node2Step1_checked :
    checkReplacement table4 root3Node2Domains0 root3Node2Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node2Step1Chunk0_0_checked, root3Node2Step1Chunk0_1_checked, root3Node2Step1Chunk0_2_checked, root3Node2Step1Chunk0_3_checked, root3Node2Step1Chunk0_4_checked, root3Node2Step1Chunk0_5_checked, root3Node2Step1Chunk1_0_checked, root3Node2Step1Chunk1_1_checked, root3Node2Step1Chunk1_2_checked, root3Node2Step1Chunk1_3_checked, root3Node2Step1Chunk1_4_checked, root3Node2Step1Chunk1_5_checked, root3Node2Step1Chunk2_0_checked, root3Node2Step1Chunk2_1_checked, root3Node2Step1Chunk2_2_checked, root3Node2Step1Chunk2_3_checked, root3Node2Step1Chunk2_4_checked, root3Node2Step1Chunk2_5_checked, root3Node2Step1Chunk3_0_checked, root3Node2Step1Chunk3_1_checked, root3Node2Step1Chunk3_2_checked, root3Node2Step1Chunk3_3_checked, root3Node2Step1Chunk3_4_checked, root3Node2Step1Chunk3_5_checked, root3Node2Step1Chunk4_0_checked, root3Node2Step1Chunk4_1_checked, root3Node2Step1Chunk4_2_checked, root3Node2Step1Chunk4_3_checked, root3Node2Step1Chunk4_4_checked, root3Node2Step1Chunk4_5_checked, root3Node2Step1Chunk5_0_checked, root3Node2Step1Chunk5_1_checked, root3Node2Step1Chunk5_2_checked, root3Node2Step1Chunk5_3_checked, root3Node2Step1Chunk5_4_checked, root3Node2Step1Chunk5_5_checked, root3Node2Step1Chunk6_0_checked, root3Node2Step1Chunk6_1_checked, root3Node2Step1Chunk6_2_checked, root3Node2Step1Chunk6_3_checked, root3Node2Step1Chunk6_4_checked, root3Node2Step1Chunk6_5_checked, root3Node2Step1Chunk7_0_checked, root3Node2Step1Chunk7_1_checked, root3Node2Step1Chunk7_2_checked, root3Node2Step1Chunk7_3_checked, root3Node2Step1Chunk7_4_checked, root3Node2Step1Chunk7_5_checked, root3Node2Step1Chunk8_0_checked, root3Node2Step1Chunk8_1_checked, root3Node2Step1Chunk8_2_checked, root3Node2Step1Chunk8_3_checked, root3Node2Step1Chunk8_4_checked, root3Node2Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root3Node2Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node2Domains1 (.output 1) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
