module

public import SpectreFinite.RadiusThreeRoot7Part44
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable4
public import SpectreFinite.RadiusThreeTable9

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node68Domains3 (v : Fin 37) : List State :=
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
  | 13 => [(3,4)]
  | 14 => [(6,3)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(1,1)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(4,0)]
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(5,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2)]
  | _ => [(5,3)]
def root7Node68Domains3Fast (v : Fin 37) : Option (List State) :=
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
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(1,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(5,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root7Node68Domains3_fast_eq : root7Node68Domains3 = expandDomains root7Node68Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node68Domains3 v = expandDomains root7Node68Domains3Fast v from by decide) v
theorem root7Node68Step3Chunk0_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_0⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk0_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_1⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk0_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_2⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk0_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_3⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk0_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_4⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk0_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_5⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk1_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_0⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk1_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_1⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk1_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_2⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk1_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_3⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk1_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_4⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk1_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_5⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk2_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_0⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk2_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_1⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk2_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_2⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk2_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_3⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk2_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_4⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk2_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_5⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk3_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_0⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk3_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_1⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk3_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_2⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk3_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_3⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk3_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_4⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk3_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_5⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk4_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_0⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk4_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_1⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk4_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_2⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk4_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_3⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk4_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_4⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk4_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_5⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk5_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_0⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk5_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_1⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk5_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_2⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk5_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_3⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk5_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_4⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk5_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_5⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk6_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_0⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk6_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_1⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk6_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_2⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk6_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_3⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk6_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_4⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk6_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_5⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk7_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_0⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk7_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_1⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk7_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_2⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk7_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_3⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk7_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_4⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk7_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_5⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk8_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_0⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk8_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_1⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk8_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_2⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk8_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_3⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk8_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_4⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3Chunk8_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_5⟩
      root7Node68Domains2 root7Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node68Domains2 root7Node68Domains3
    root7Node68Domains2Fast root7Node68Domains3Fast
    root7Node68Domains2_fast_eq root7Node68Domains3_fast_eq (by decide)
theorem root7Node68Step3_checked :
    checkReplacement table9 root7Node68Domains2 root7Node68Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node68Step3Chunk0_0_checked, root7Node68Step3Chunk0_1_checked, root7Node68Step3Chunk0_2_checked, root7Node68Step3Chunk0_3_checked, root7Node68Step3Chunk0_4_checked, root7Node68Step3Chunk0_5_checked, root7Node68Step3Chunk1_0_checked, root7Node68Step3Chunk1_1_checked, root7Node68Step3Chunk1_2_checked, root7Node68Step3Chunk1_3_checked, root7Node68Step3Chunk1_4_checked, root7Node68Step3Chunk1_5_checked, root7Node68Step3Chunk2_0_checked, root7Node68Step3Chunk2_1_checked, root7Node68Step3Chunk2_2_checked, root7Node68Step3Chunk2_3_checked, root7Node68Step3Chunk2_4_checked, root7Node68Step3Chunk2_5_checked, root7Node68Step3Chunk3_0_checked, root7Node68Step3Chunk3_1_checked, root7Node68Step3Chunk3_2_checked, root7Node68Step3Chunk3_3_checked, root7Node68Step3Chunk3_4_checked, root7Node68Step3Chunk3_5_checked, root7Node68Step3Chunk4_0_checked, root7Node68Step3Chunk4_1_checked, root7Node68Step3Chunk4_2_checked, root7Node68Step3Chunk4_3_checked, root7Node68Step3Chunk4_4_checked, root7Node68Step3Chunk4_5_checked, root7Node68Step3Chunk5_0_checked, root7Node68Step3Chunk5_1_checked, root7Node68Step3Chunk5_2_checked, root7Node68Step3Chunk5_3_checked, root7Node68Step3Chunk5_4_checked, root7Node68Step3Chunk5_5_checked, root7Node68Step3Chunk6_0_checked, root7Node68Step3Chunk6_1_checked, root7Node68Step3Chunk6_2_checked, root7Node68Step3Chunk6_3_checked, root7Node68Step3Chunk6_4_checked, root7Node68Step3Chunk6_5_checked, root7Node68Step3Chunk7_0_checked, root7Node68Step3Chunk7_1_checked, root7Node68Step3Chunk7_2_checked, root7Node68Step3Chunk7_3_checked, root7Node68Step3Chunk7_4_checked, root7Node68Step3Chunk7_5_checked, root7Node68Step3Chunk8_0_checked, root7Node68Step3Chunk8_1_checked, root7Node68Step3Chunk8_2_checked, root7Node68Step3Chunk8_3_checked, root7Node68Step3Chunk8_4_checked, root7Node68Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node69Domains0 : Domains 37 State := restrict root7Node68Domains3 9 (1,1)
def root7Node69Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(1,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(5,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root7Node69Domains0_fast_eq : root7Node69Domains0 = expandDomains root7Node69Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node69Domains0 v = expandDomains root7Node69Domains0Fast v from by decide) v
def root7Node69Domains1 (v : Fin 37) : List State :=
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
  | 13 => [(3,4)]
  | 14 => [(6,3)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(1,1)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(4,0)]
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(5,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2)]
  | _ => [(5,3)]
def root7Node69Domains1Fast (v : Fin 37) : Option (List State) :=
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
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(1,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(5,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root7Node69Domains1_fast_eq : root7Node69Domains1 = expandDomains root7Node69Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node69Domains1 v = expandDomains root7Node69Domains1Fast v from by decide) v
theorem root7Node69Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root7Node69Domains0 root7Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node69Domains0 root7Node69Domains1
    root7Node69Domains0Fast root7Node69Domains1Fast
    root7Node69Domains0_fast_eq root7Node69Domains1_fast_eq (by decide)
theorem root7Node69Step1_checked :
    checkReplacement table4 root7Node69Domains0 root7Node69Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node69Step1Chunk0_0_checked, root7Node69Step1Chunk0_1_checked, root7Node69Step1Chunk0_2_checked, root7Node69Step1Chunk0_3_checked, root7Node69Step1Chunk0_4_checked, root7Node69Step1Chunk0_5_checked, root7Node69Step1Chunk1_0_checked, root7Node69Step1Chunk1_1_checked, root7Node69Step1Chunk1_2_checked, root7Node69Step1Chunk1_3_checked, root7Node69Step1Chunk1_4_checked, root7Node69Step1Chunk1_5_checked, root7Node69Step1Chunk2_0_checked, root7Node69Step1Chunk2_1_checked, root7Node69Step1Chunk2_2_checked, root7Node69Step1Chunk2_3_checked, root7Node69Step1Chunk2_4_checked, root7Node69Step1Chunk2_5_checked, root7Node69Step1Chunk3_0_checked, root7Node69Step1Chunk3_1_checked, root7Node69Step1Chunk3_2_checked, root7Node69Step1Chunk3_3_checked, root7Node69Step1Chunk3_4_checked, root7Node69Step1Chunk3_5_checked, root7Node69Step1Chunk4_0_checked, root7Node69Step1Chunk4_1_checked, root7Node69Step1Chunk4_2_checked, root7Node69Step1Chunk4_3_checked, root7Node69Step1Chunk4_4_checked, root7Node69Step1Chunk4_5_checked, root7Node69Step1Chunk5_0_checked, root7Node69Step1Chunk5_1_checked, root7Node69Step1Chunk5_2_checked, root7Node69Step1Chunk5_3_checked, root7Node69Step1Chunk5_4_checked, root7Node69Step1Chunk5_5_checked, root7Node69Step1Chunk6_0_checked, root7Node69Step1Chunk6_1_checked, root7Node69Step1Chunk6_2_checked, root7Node69Step1Chunk6_3_checked, root7Node69Step1Chunk6_4_checked, root7Node69Step1Chunk6_5_checked, root7Node69Step1Chunk7_0_checked, root7Node69Step1Chunk7_1_checked, root7Node69Step1Chunk7_2_checked, root7Node69Step1Chunk7_3_checked, root7Node69Step1Chunk7_4_checked, root7Node69Step1Chunk7_5_checked, root7Node69Step1Chunk8_0_checked, root7Node69Step1Chunk8_1_checked, root7Node69Step1Chunk8_2_checked, root7Node69Step1Chunk8_3_checked, root7Node69Step1Chunk8_4_checked, root7Node69Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node70Domains0 : Domains 37 State := restrict root7Node69Domains1 33 (4,0)
def root7Node70Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(1,1)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(5,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root7Node70Domains0_fast_eq : root7Node70Domains0 = expandDomains root7Node70Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node70Domains0 v = expandDomains root7Node70Domains0Fast v from by decide) v
theorem root7Node70Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node70Domains0 (.output 33) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
