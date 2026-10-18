module

public import SpectreFinite.RadiusThreeRoot1Part17
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable25
public import SpectreFinite.RadiusThreeTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node30Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3),(6,3)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1)]
  | 20 => [(0,2)]
  | 21 => [(0,4),(1,1)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2)]
  | 27 => [(4,0)]
  | 28 => [(6,0),(6,5)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,0),(7,0)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root1Node30Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3),(6,3)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1)]
  | 20 => some [(0,2)]
  | 21 => some [(0,4),(1,1)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0),(6,5)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0),(7,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root1Node30Domains4_fast_eq : root1Node30Domains4 = expandDomains root1Node30Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node30Domains4 v = expandDomains root1Node30Domains4Fast v from by decide) v
theorem root1Node30Step4Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root1Node30Domains3 root1Node30Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains3 root1Node30Domains4
    root1Node30Domains3Fast root1Node30Domains4Fast
    root1Node30Domains3_fast_eq root1Node30Domains4_fast_eq (by decide)
theorem root1Node30Step4_checked :
    checkReplacement table25 root1Node30Domains3 root1Node30Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node30Step4Chunk0_0_checked, root1Node30Step4Chunk0_1_checked, root1Node30Step4Chunk0_2_checked, root1Node30Step4Chunk0_3_checked, root1Node30Step4Chunk0_4_checked, root1Node30Step4Chunk0_5_checked, root1Node30Step4Chunk1_0_checked, root1Node30Step4Chunk1_1_checked, root1Node30Step4Chunk1_2_checked, root1Node30Step4Chunk1_3_checked, root1Node30Step4Chunk1_4_checked, root1Node30Step4Chunk1_5_checked, root1Node30Step4Chunk2_0_checked, root1Node30Step4Chunk2_1_checked, root1Node30Step4Chunk2_2_checked, root1Node30Step4Chunk2_3_checked, root1Node30Step4Chunk2_4_checked, root1Node30Step4Chunk2_5_checked, root1Node30Step4Chunk3_0_checked, root1Node30Step4Chunk3_1_checked, root1Node30Step4Chunk3_2_checked, root1Node30Step4Chunk3_3_checked, root1Node30Step4Chunk3_4_checked, root1Node30Step4Chunk3_5_checked, root1Node30Step4Chunk4_0_checked, root1Node30Step4Chunk4_1_checked, root1Node30Step4Chunk4_2_checked, root1Node30Step4Chunk4_3_checked, root1Node30Step4Chunk4_4_checked, root1Node30Step4Chunk4_5_checked, root1Node30Step4Chunk5_0_checked, root1Node30Step4Chunk5_1_checked, root1Node30Step4Chunk5_2_checked, root1Node30Step4Chunk5_3_checked, root1Node30Step4Chunk5_4_checked, root1Node30Step4Chunk5_5_checked, root1Node30Step4Chunk6_0_checked, root1Node30Step4Chunk6_1_checked, root1Node30Step4Chunk6_2_checked, root1Node30Step4Chunk6_3_checked, root1Node30Step4Chunk6_4_checked, root1Node30Step4Chunk6_5_checked, root1Node30Step4Chunk7_0_checked, root1Node30Step4Chunk7_1_checked, root1Node30Step4Chunk7_2_checked, root1Node30Step4Chunk7_3_checked, root1Node30Step4Chunk7_4_checked, root1Node30Step4Chunk7_5_checked, root1Node30Step4Chunk8_0_checked, root1Node30Step4Chunk8_1_checked, root1Node30Step4Chunk8_2_checked, root1Node30Step4Chunk8_3_checked, root1Node30Step4Chunk8_4_checked, root1Node30Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node30Domains5 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3),(6,3)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1)]
  | 20 => [(0,2)]
  | 21 => [(0,4),(1,1)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2)]
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
def root1Node30Domains5Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3),(6,3)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1)]
  | 20 => some [(0,2)]
  | 21 => some [(0,4),(1,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2)]
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
theorem root1Node30Domains5_fast_eq : root1Node30Domains5 = expandDomains root1Node30Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node30Domains5 v = expandDomains root1Node30Domains5Fast v from by decide) v
theorem root1Node30Step5Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root1Node30Domains4 root1Node30Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains4 root1Node30Domains5
    root1Node30Domains4Fast root1Node30Domains5Fast
    root1Node30Domains4_fast_eq root1Node30Domains5_fast_eq (by decide)
theorem root1Node30Step5_checked :
    checkReplacement table22 root1Node30Domains4 root1Node30Domains5 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node30Step5Chunk0_0_checked, root1Node30Step5Chunk0_1_checked, root1Node30Step5Chunk0_2_checked, root1Node30Step5Chunk0_3_checked, root1Node30Step5Chunk0_4_checked, root1Node30Step5Chunk0_5_checked, root1Node30Step5Chunk1_0_checked, root1Node30Step5Chunk1_1_checked, root1Node30Step5Chunk1_2_checked, root1Node30Step5Chunk1_3_checked, root1Node30Step5Chunk1_4_checked, root1Node30Step5Chunk1_5_checked, root1Node30Step5Chunk2_0_checked, root1Node30Step5Chunk2_1_checked, root1Node30Step5Chunk2_2_checked, root1Node30Step5Chunk2_3_checked, root1Node30Step5Chunk2_4_checked, root1Node30Step5Chunk2_5_checked, root1Node30Step5Chunk3_0_checked, root1Node30Step5Chunk3_1_checked, root1Node30Step5Chunk3_2_checked, root1Node30Step5Chunk3_3_checked, root1Node30Step5Chunk3_4_checked, root1Node30Step5Chunk3_5_checked, root1Node30Step5Chunk4_0_checked, root1Node30Step5Chunk4_1_checked, root1Node30Step5Chunk4_2_checked, root1Node30Step5Chunk4_3_checked, root1Node30Step5Chunk4_4_checked, root1Node30Step5Chunk4_5_checked, root1Node30Step5Chunk5_0_checked, root1Node30Step5Chunk5_1_checked, root1Node30Step5Chunk5_2_checked, root1Node30Step5Chunk5_3_checked, root1Node30Step5Chunk5_4_checked, root1Node30Step5Chunk5_5_checked, root1Node30Step5Chunk6_0_checked, root1Node30Step5Chunk6_1_checked, root1Node30Step5Chunk6_2_checked, root1Node30Step5Chunk6_3_checked, root1Node30Step5Chunk6_4_checked, root1Node30Step5Chunk6_5_checked, root1Node30Step5Chunk7_0_checked, root1Node30Step5Chunk7_1_checked, root1Node30Step5Chunk7_2_checked, root1Node30Step5Chunk7_3_checked, root1Node30Step5Chunk7_4_checked, root1Node30Step5Chunk7_5_checked, root1Node30Step5Chunk8_0_checked, root1Node30Step5Chunk8_1_checked, root1Node30Step5Chunk8_2_checked, root1Node30Step5Chunk8_3_checked, root1Node30Step5Chunk8_4_checked, root1Node30Step5Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node30Domains6 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1)]
  | 20 => [(0,2)]
  | 21 => [(1,1)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2)]
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
def root1Node30Domains6Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2)]
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
theorem root1Node30Domains6_fast_eq : root1Node30Domains6 = expandDomains root1Node30Domains6Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node30Domains6 v = expandDomains root1Node30Domains6Fast v from by decide) v
theorem root1Node30Step6Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root1Node30Domains5 root1Node30Domains6 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains5 root1Node30Domains6
    root1Node30Domains5Fast root1Node30Domains6Fast
    root1Node30Domains5_fast_eq root1Node30Domains6_fast_eq (by decide)
theorem root1Node30Step6_checked :
    checkReplacement table8 root1Node30Domains5 root1Node30Domains6 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node30Step6Chunk0_0_checked, root1Node30Step6Chunk0_1_checked, root1Node30Step6Chunk0_2_checked, root1Node30Step6Chunk0_3_checked, root1Node30Step6Chunk0_4_checked, root1Node30Step6Chunk0_5_checked, root1Node30Step6Chunk1_0_checked, root1Node30Step6Chunk1_1_checked, root1Node30Step6Chunk1_2_checked, root1Node30Step6Chunk1_3_checked, root1Node30Step6Chunk1_4_checked, root1Node30Step6Chunk1_5_checked, root1Node30Step6Chunk2_0_checked, root1Node30Step6Chunk2_1_checked, root1Node30Step6Chunk2_2_checked, root1Node30Step6Chunk2_3_checked, root1Node30Step6Chunk2_4_checked, root1Node30Step6Chunk2_5_checked, root1Node30Step6Chunk3_0_checked, root1Node30Step6Chunk3_1_checked, root1Node30Step6Chunk3_2_checked, root1Node30Step6Chunk3_3_checked, root1Node30Step6Chunk3_4_checked, root1Node30Step6Chunk3_5_checked, root1Node30Step6Chunk4_0_checked, root1Node30Step6Chunk4_1_checked, root1Node30Step6Chunk4_2_checked, root1Node30Step6Chunk4_3_checked, root1Node30Step6Chunk4_4_checked, root1Node30Step6Chunk4_5_checked, root1Node30Step6Chunk5_0_checked, root1Node30Step6Chunk5_1_checked, root1Node30Step6Chunk5_2_checked, root1Node30Step6Chunk5_3_checked, root1Node30Step6Chunk5_4_checked, root1Node30Step6Chunk5_5_checked, root1Node30Step6Chunk6_0_checked, root1Node30Step6Chunk6_1_checked, root1Node30Step6Chunk6_2_checked, root1Node30Step6Chunk6_3_checked, root1Node30Step6Chunk6_4_checked, root1Node30Step6Chunk6_5_checked, root1Node30Step6Chunk7_0_checked, root1Node30Step6Chunk7_1_checked, root1Node30Step6Chunk7_2_checked, root1Node30Step6Chunk7_3_checked, root1Node30Step6Chunk7_4_checked, root1Node30Step6Chunk7_5_checked, root1Node30Step6Chunk8_0_checked, root1Node30Step6Chunk8_1_checked, root1Node30Step6Chunk8_2_checked, root1Node30Step6Chunk8_3_checked, root1Node30Step6Chunk8_4_checked, root1Node30Step6Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
