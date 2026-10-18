module

public import SpectreFinite.RadiusThreeRoot4Part22
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node38Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(6,4)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,3)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0),(8,0)]
  | 29 => [(8,3)]
  | 30 => [(5,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5)]
  | 35 => [(4,4)]
  | _ => [(0,0)]
def root4Node38Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0),(8,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5)]
  | 35 => some [(4,4)]
  | _ => some [(0,0)]
theorem root4Node38Domains3_fast_eq : root4Node38Domains3 = expandDomains root4Node38Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node38Domains3 v = expandDomains root4Node38Domains3Fast v from by decide) v
theorem root4Node38Step3Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root4Node38Domains2 root4Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains2 root4Node38Domains3
    root4Node38Domains2Fast root4Node38Domains3Fast
    root4Node38Domains2_fast_eq root4Node38Domains3_fast_eq (by decide)
theorem root4Node38Step3_checked :
    checkReplacement table8 root4Node38Domains2 root4Node38Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node38Step3Chunk0_0_checked, root4Node38Step3Chunk0_1_checked, root4Node38Step3Chunk0_2_checked, root4Node38Step3Chunk0_3_checked, root4Node38Step3Chunk0_4_checked, root4Node38Step3Chunk0_5_checked, root4Node38Step3Chunk1_0_checked, root4Node38Step3Chunk1_1_checked, root4Node38Step3Chunk1_2_checked, root4Node38Step3Chunk1_3_checked, root4Node38Step3Chunk1_4_checked, root4Node38Step3Chunk1_5_checked, root4Node38Step3Chunk2_0_checked, root4Node38Step3Chunk2_1_checked, root4Node38Step3Chunk2_2_checked, root4Node38Step3Chunk2_3_checked, root4Node38Step3Chunk2_4_checked, root4Node38Step3Chunk2_5_checked, root4Node38Step3Chunk3_0_checked, root4Node38Step3Chunk3_1_checked, root4Node38Step3Chunk3_2_checked, root4Node38Step3Chunk3_3_checked, root4Node38Step3Chunk3_4_checked, root4Node38Step3Chunk3_5_checked, root4Node38Step3Chunk4_0_checked, root4Node38Step3Chunk4_1_checked, root4Node38Step3Chunk4_2_checked, root4Node38Step3Chunk4_3_checked, root4Node38Step3Chunk4_4_checked, root4Node38Step3Chunk4_5_checked, root4Node38Step3Chunk5_0_checked, root4Node38Step3Chunk5_1_checked, root4Node38Step3Chunk5_2_checked, root4Node38Step3Chunk5_3_checked, root4Node38Step3Chunk5_4_checked, root4Node38Step3Chunk5_5_checked, root4Node38Step3Chunk6_0_checked, root4Node38Step3Chunk6_1_checked, root4Node38Step3Chunk6_2_checked, root4Node38Step3Chunk6_3_checked, root4Node38Step3Chunk6_4_checked, root4Node38Step3Chunk6_5_checked, root4Node38Step3Chunk7_0_checked, root4Node38Step3Chunk7_1_checked, root4Node38Step3Chunk7_2_checked, root4Node38Step3Chunk7_3_checked, root4Node38Step3Chunk7_4_checked, root4Node38Step3Chunk7_5_checked, root4Node38Step3Chunk8_0_checked, root4Node38Step3Chunk8_1_checked, root4Node38Step3Chunk8_2_checked, root4Node38Step3Chunk8_3_checked, root4Node38Step3Chunk8_4_checked, root4Node38Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node38Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(6,4)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,3)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4)]
  | 28 => [(8,0)]
  | 29 => [(8,3)]
  | 30 => [(5,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1)]
  | 33 => [(1,4)]
  | 34 => [(0,5)]
  | 35 => [(4,4)]
  | _ => [(0,0)]
def root4Node38Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4)]
  | 28 => some [(8,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(4,4)]
  | _ => some [(0,0)]
theorem root4Node38Domains4_fast_eq : root4Node38Domains4 = expandDomains root4Node38Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node38Domains4 v = expandDomains root4Node38Domains4Fast v from by decide) v
theorem root4Node38Step4Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root4Node38Domains3 root4Node38Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains3 root4Node38Domains4
    root4Node38Domains3Fast root4Node38Domains4Fast
    root4Node38Domains3_fast_eq root4Node38Domains4_fast_eq (by decide)
theorem root4Node38Step4_checked :
    checkReplacement table22 root4Node38Domains3 root4Node38Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node38Step4Chunk0_0_checked, root4Node38Step4Chunk0_1_checked, root4Node38Step4Chunk0_2_checked, root4Node38Step4Chunk0_3_checked, root4Node38Step4Chunk0_4_checked, root4Node38Step4Chunk0_5_checked, root4Node38Step4Chunk1_0_checked, root4Node38Step4Chunk1_1_checked, root4Node38Step4Chunk1_2_checked, root4Node38Step4Chunk1_3_checked, root4Node38Step4Chunk1_4_checked, root4Node38Step4Chunk1_5_checked, root4Node38Step4Chunk2_0_checked, root4Node38Step4Chunk2_1_checked, root4Node38Step4Chunk2_2_checked, root4Node38Step4Chunk2_3_checked, root4Node38Step4Chunk2_4_checked, root4Node38Step4Chunk2_5_checked, root4Node38Step4Chunk3_0_checked, root4Node38Step4Chunk3_1_checked, root4Node38Step4Chunk3_2_checked, root4Node38Step4Chunk3_3_checked, root4Node38Step4Chunk3_4_checked, root4Node38Step4Chunk3_5_checked, root4Node38Step4Chunk4_0_checked, root4Node38Step4Chunk4_1_checked, root4Node38Step4Chunk4_2_checked, root4Node38Step4Chunk4_3_checked, root4Node38Step4Chunk4_4_checked, root4Node38Step4Chunk4_5_checked, root4Node38Step4Chunk5_0_checked, root4Node38Step4Chunk5_1_checked, root4Node38Step4Chunk5_2_checked, root4Node38Step4Chunk5_3_checked, root4Node38Step4Chunk5_4_checked, root4Node38Step4Chunk5_5_checked, root4Node38Step4Chunk6_0_checked, root4Node38Step4Chunk6_1_checked, root4Node38Step4Chunk6_2_checked, root4Node38Step4Chunk6_3_checked, root4Node38Step4Chunk6_4_checked, root4Node38Step4Chunk6_5_checked, root4Node38Step4Chunk7_0_checked, root4Node38Step4Chunk7_1_checked, root4Node38Step4Chunk7_2_checked, root4Node38Step4Chunk7_3_checked, root4Node38Step4Chunk7_4_checked, root4Node38Step4Chunk7_5_checked, root4Node38Step4Chunk8_0_checked, root4Node38Step4Chunk8_1_checked, root4Node38Step4Chunk8_2_checked, root4Node38Step4Chunk8_3_checked, root4Node38Step4Chunk8_4_checked, root4Node38Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node39Domains0 : Domains 37 State := restrict root4Node38Domains4 2 (5,2)
def root4Node39Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4)]
  | 28 => some [(8,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(4,4)]
  | _ => some [(0,0)]
theorem root4Node39Domains0_fast_eq : root4Node39Domains0 = expandDomains root4Node39Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node39Domains0 v = expandDomains root4Node39Domains0Fast v from by decide) v
end SpectreFinite.HexSearch.RadiusThree
