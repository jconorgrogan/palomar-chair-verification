module

public import SpectreFinite.RadiusThreeRoot8Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node30Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(1,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(8,1)]
  | 14 => [(6,5)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(3,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(8,0)]
  | 34 => [(7,3)]
  | 35 => [(8,2)]
  | _ => [(5,0)]
def root8Node30Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(1,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root8Node30Domains4_fast_eq : root8Node30Domains4 = expandDomains root8Node30Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node30Domains4 v = expandDomains root8Node30Domains4Fast v from by decide) v
theorem root8Node30Step4Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root8Node30Domains3 root8Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains3 root8Node30Domains4
    root8Node30Domains3Fast root8Node30Domains4Fast
    root8Node30Domains3_fast_eq root8Node30Domains4_fast_eq (by decide)
theorem root8Node30Step4_checked :
    checkReplacement table26 root8Node30Domains3 root8Node30Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node30Step4Chunk0_0_checked, root8Node30Step4Chunk0_1_checked, root8Node30Step4Chunk0_2_checked, root8Node30Step4Chunk0_3_checked, root8Node30Step4Chunk0_4_checked, root8Node30Step4Chunk0_5_checked, root8Node30Step4Chunk1_0_checked, root8Node30Step4Chunk1_1_checked, root8Node30Step4Chunk1_2_checked, root8Node30Step4Chunk1_3_checked, root8Node30Step4Chunk1_4_checked, root8Node30Step4Chunk1_5_checked, root8Node30Step4Chunk2_0_checked, root8Node30Step4Chunk2_1_checked, root8Node30Step4Chunk2_2_checked, root8Node30Step4Chunk2_3_checked, root8Node30Step4Chunk2_4_checked, root8Node30Step4Chunk2_5_checked, root8Node30Step4Chunk3_0_checked, root8Node30Step4Chunk3_1_checked, root8Node30Step4Chunk3_2_checked, root8Node30Step4Chunk3_3_checked, root8Node30Step4Chunk3_4_checked, root8Node30Step4Chunk3_5_checked, root8Node30Step4Chunk4_0_checked, root8Node30Step4Chunk4_1_checked, root8Node30Step4Chunk4_2_checked, root8Node30Step4Chunk4_3_checked, root8Node30Step4Chunk4_4_checked, root8Node30Step4Chunk4_5_checked, root8Node30Step4Chunk5_0_checked, root8Node30Step4Chunk5_1_checked, root8Node30Step4Chunk5_2_checked, root8Node30Step4Chunk5_3_checked, root8Node30Step4Chunk5_4_checked, root8Node30Step4Chunk5_5_checked, root8Node30Step4Chunk6_0_checked, root8Node30Step4Chunk6_1_checked, root8Node30Step4Chunk6_2_checked, root8Node30Step4Chunk6_3_checked, root8Node30Step4Chunk6_4_checked, root8Node30Step4Chunk6_5_checked, root8Node30Step4Chunk7_0_checked, root8Node30Step4Chunk7_1_checked, root8Node30Step4Chunk7_2_checked, root8Node30Step4Chunk7_3_checked, root8Node30Step4Chunk7_4_checked, root8Node30Step4Chunk7_5_checked, root8Node30Step4Chunk8_0_checked, root8Node30Step4Chunk8_1_checked, root8Node30Step4Chunk8_2_checked, root8Node30Step4Chunk8_3_checked, root8Node30Step4Chunk8_4_checked, root8Node30Step4Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node30Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node30Domains4 (.output 14) = true := by decide
def root8Node31Domains0 : Domains 37 State := restrict root8Node25Domains1 9 (6,1)
def root8Node31Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(8,1)]
  | 14 => some [(0,2),(6,5)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(3,0),(5,0),(7,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root8Node31Domains0_fast_eq : root8Node31Domains0 = expandDomains root8Node31Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node31Domains0 v = expandDomains root8Node31Domains0Fast v from by decide) v
def root8Node31Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1),(8,1)]
  | 14 => [(0,2),(6,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(3,0),(5,0),(7,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(8,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(7,1),(8,1)]
  | 33 => [(4,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2),(8,2)]
  | _ => [(5,0),(5,3),(8,0)]
def root8Node31Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(8,1)]
  | 14 => some [(0,2),(6,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(3,0),(5,0),(7,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root8Node31Domains1_fast_eq : root8Node31Domains1 = expandDomains root8Node31Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node31Domains1 v = expandDomains root8Node31Domains1Fast v from by decide) v
theorem root8Node31Step1Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1_checked :
    checkReplacement table22 root8Node31Domains0 root8Node31Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node31Step1Chunk0_0_checked, root8Node31Step1Chunk0_1_checked, root8Node31Step1Chunk0_2_checked, root8Node31Step1Chunk0_3_checked, root8Node31Step1Chunk0_4_checked, root8Node31Step1Chunk0_5_checked, root8Node31Step1Chunk1_0_checked, root8Node31Step1Chunk1_1_checked, root8Node31Step1Chunk1_2_checked, root8Node31Step1Chunk1_3_checked, root8Node31Step1Chunk1_4_checked, root8Node31Step1Chunk1_5_checked, root8Node31Step1Chunk2_0_checked, root8Node31Step1Chunk2_1_checked, root8Node31Step1Chunk2_2_checked, root8Node31Step1Chunk2_3_checked, root8Node31Step1Chunk2_4_checked, root8Node31Step1Chunk2_5_checked, root8Node31Step1Chunk3_0_checked, root8Node31Step1Chunk3_1_checked, root8Node31Step1Chunk3_2_checked, root8Node31Step1Chunk3_3_checked, root8Node31Step1Chunk3_4_checked, root8Node31Step1Chunk3_5_checked, root8Node31Step1Chunk4_0_checked, root8Node31Step1Chunk4_1_checked, root8Node31Step1Chunk4_2_checked, root8Node31Step1Chunk4_3_checked, root8Node31Step1Chunk4_4_checked, root8Node31Step1Chunk4_5_checked, root8Node31Step1Chunk5_0_checked, root8Node31Step1Chunk5_1_checked, root8Node31Step1Chunk5_2_checked, root8Node31Step1Chunk5_3_checked, root8Node31Step1Chunk5_4_checked, root8Node31Step1Chunk5_5_checked, root8Node31Step1Chunk6_0_checked, root8Node31Step1Chunk6_1_checked, root8Node31Step1Chunk6_2_checked, root8Node31Step1Chunk6_3_checked, root8Node31Step1Chunk6_4_checked, root8Node31Step1Chunk6_5_checked, root8Node31Step1Chunk7_0_checked, root8Node31Step1Chunk7_1_checked, root8Node31Step1Chunk7_2_checked, root8Node31Step1Chunk7_3_checked, root8Node31Step1Chunk7_4_checked, root8Node31Step1Chunk7_5_checked, root8Node31Step1Chunk8_0_checked, root8Node31Step1Chunk8_1_checked, root8Node31Step1Chunk8_2_checked, root8Node31Step1Chunk8_3_checked, root8Node31Step1Chunk8_4_checked, root8Node31Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node32Domains0 : Domains 37 State := restrict root8Node31Domains1 13 (4,1)
def root8Node32Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2),(6,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(3,0),(5,0),(7,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root8Node32Domains0_fast_eq : root8Node32Domains0 = expandDomains root8Node32Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node32Domains0 v = expandDomains root8Node32Domains0Fast v from by decide) v
def root8Node32Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(5,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(8,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(8,1)]
  | 33 => [(4,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2)]
  | _ => [(5,3)]
def root8Node32Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node32Domains1_fast_eq : root8Node32Domains1 = expandDomains root8Node32Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node32Domains1 v = expandDomains root8Node32Domains1Fast v from by decide) v
theorem root8Node32Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root8Node32Domains0 root8Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains0 root8Node32Domains1
    root8Node32Domains0Fast root8Node32Domains1Fast
    root8Node32Domains0_fast_eq root8Node32Domains1_fast_eq (by decide)
theorem root8Node32Step1_checked :
    checkReplacement table26 root8Node32Domains0 root8Node32Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node32Step1Chunk0_0_checked, root8Node32Step1Chunk0_1_checked, root8Node32Step1Chunk0_2_checked, root8Node32Step1Chunk0_3_checked, root8Node32Step1Chunk0_4_checked, root8Node32Step1Chunk0_5_checked, root8Node32Step1Chunk1_0_checked, root8Node32Step1Chunk1_1_checked, root8Node32Step1Chunk1_2_checked, root8Node32Step1Chunk1_3_checked, root8Node32Step1Chunk1_4_checked, root8Node32Step1Chunk1_5_checked, root8Node32Step1Chunk2_0_checked, root8Node32Step1Chunk2_1_checked, root8Node32Step1Chunk2_2_checked, root8Node32Step1Chunk2_3_checked, root8Node32Step1Chunk2_4_checked, root8Node32Step1Chunk2_5_checked, root8Node32Step1Chunk3_0_checked, root8Node32Step1Chunk3_1_checked, root8Node32Step1Chunk3_2_checked, root8Node32Step1Chunk3_3_checked, root8Node32Step1Chunk3_4_checked, root8Node32Step1Chunk3_5_checked, root8Node32Step1Chunk4_0_checked, root8Node32Step1Chunk4_1_checked, root8Node32Step1Chunk4_2_checked, root8Node32Step1Chunk4_3_checked, root8Node32Step1Chunk4_4_checked, root8Node32Step1Chunk4_5_checked, root8Node32Step1Chunk5_0_checked, root8Node32Step1Chunk5_1_checked, root8Node32Step1Chunk5_2_checked, root8Node32Step1Chunk5_3_checked, root8Node32Step1Chunk5_4_checked, root8Node32Step1Chunk5_5_checked, root8Node32Step1Chunk6_0_checked, root8Node32Step1Chunk6_1_checked, root8Node32Step1Chunk6_2_checked, root8Node32Step1Chunk6_3_checked, root8Node32Step1Chunk6_4_checked, root8Node32Step1Chunk6_5_checked, root8Node32Step1Chunk7_0_checked, root8Node32Step1Chunk7_1_checked, root8Node32Step1Chunk7_2_checked, root8Node32Step1Chunk7_3_checked, root8Node32Step1Chunk7_4_checked, root8Node32Step1Chunk7_5_checked, root8Node32Step1Chunk8_0_checked, root8Node32Step1Chunk8_1_checked, root8Node32Step1Chunk8_2_checked, root8Node32Step1Chunk8_3_checked, root8Node32Step1Chunk8_4_checked, root8Node32Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node32Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node32Domains1 (.output 15) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
