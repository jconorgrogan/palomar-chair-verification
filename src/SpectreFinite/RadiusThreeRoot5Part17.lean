module

public import SpectreFinite.RadiusThreeRoot5Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable23
public import SpectreFinite.RadiusThreeTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node30Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(2,0)]
  | 8 => [(7,3)]
  | 9 => [(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(3,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0)]
  | 21 => [(7,1)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node30Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(2,0)]
  | 8 => some [(7,3)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node30Domains3_fast_eq : root5Node30Domains3 = expandDomains root5Node30Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node30Domains3 v = expandDomains root5Node30Domains3Fast v from by decide) v
theorem root5Node30Step3Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root5Node30Domains2 root5Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains2 root5Node30Domains3
    root5Node30Domains2Fast root5Node30Domains3Fast
    root5Node30Domains2_fast_eq root5Node30Domains3_fast_eq (by decide)
theorem root5Node30Step3_checked :
    checkReplacement table4 root5Node30Domains2 root5Node30Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node30Step3Chunk0_0_checked, root5Node30Step3Chunk0_1_checked, root5Node30Step3Chunk0_2_checked, root5Node30Step3Chunk0_3_checked, root5Node30Step3Chunk0_4_checked, root5Node30Step3Chunk0_5_checked, root5Node30Step3Chunk1_0_checked, root5Node30Step3Chunk1_1_checked, root5Node30Step3Chunk1_2_checked, root5Node30Step3Chunk1_3_checked, root5Node30Step3Chunk1_4_checked, root5Node30Step3Chunk1_5_checked, root5Node30Step3Chunk2_0_checked, root5Node30Step3Chunk2_1_checked, root5Node30Step3Chunk2_2_checked, root5Node30Step3Chunk2_3_checked, root5Node30Step3Chunk2_4_checked, root5Node30Step3Chunk2_5_checked, root5Node30Step3Chunk3_0_checked, root5Node30Step3Chunk3_1_checked, root5Node30Step3Chunk3_2_checked, root5Node30Step3Chunk3_3_checked, root5Node30Step3Chunk3_4_checked, root5Node30Step3Chunk3_5_checked, root5Node30Step3Chunk4_0_checked, root5Node30Step3Chunk4_1_checked, root5Node30Step3Chunk4_2_checked, root5Node30Step3Chunk4_3_checked, root5Node30Step3Chunk4_4_checked, root5Node30Step3Chunk4_5_checked, root5Node30Step3Chunk5_0_checked, root5Node30Step3Chunk5_1_checked, root5Node30Step3Chunk5_2_checked, root5Node30Step3Chunk5_3_checked, root5Node30Step3Chunk5_4_checked, root5Node30Step3Chunk5_5_checked, root5Node30Step3Chunk6_0_checked, root5Node30Step3Chunk6_1_checked, root5Node30Step3Chunk6_2_checked, root5Node30Step3Chunk6_3_checked, root5Node30Step3Chunk6_4_checked, root5Node30Step3Chunk6_5_checked, root5Node30Step3Chunk7_0_checked, root5Node30Step3Chunk7_1_checked, root5Node30Step3Chunk7_2_checked, root5Node30Step3Chunk7_3_checked, root5Node30Step3Chunk7_4_checked, root5Node30Step3Chunk7_5_checked, root5Node30Step3Chunk8_0_checked, root5Node30Step3Chunk8_1_checked, root5Node30Step3Chunk8_2_checked, root5Node30Step3Chunk8_3_checked, root5Node30Step3Chunk8_4_checked, root5Node30Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node31Domains0 : Domains 37 State := restrict root5Node30Domains3 15 (4,0)
def root5Node31Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(2,0)]
  | 8 => some [(7,3)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node31Domains0_fast_eq : root5Node31Domains0 = expandDomains root5Node31Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node31Domains0 v = expandDomains root5Node31Domains0Fast v from by decide) v
def root5Node31Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(2,0)]
  | 8 => [(7,3)]
  | 9 => [(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(3,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0)]
  | 21 => [(7,1)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node31Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(2,0)]
  | 8 => some [(7,3)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node31Domains1_fast_eq : root5Node31Domains1 = expandDomains root5Node31Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node31Domains1 v = expandDomains root5Node31Domains1Fast v from by decide) v
theorem root5Node31Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1_checked :
    checkReplacement table23 root5Node31Domains0 root5Node31Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node31Step1Chunk0_0_checked, root5Node31Step1Chunk0_1_checked, root5Node31Step1Chunk0_2_checked, root5Node31Step1Chunk0_3_checked, root5Node31Step1Chunk0_4_checked, root5Node31Step1Chunk0_5_checked, root5Node31Step1Chunk1_0_checked, root5Node31Step1Chunk1_1_checked, root5Node31Step1Chunk1_2_checked, root5Node31Step1Chunk1_3_checked, root5Node31Step1Chunk1_4_checked, root5Node31Step1Chunk1_5_checked, root5Node31Step1Chunk2_0_checked, root5Node31Step1Chunk2_1_checked, root5Node31Step1Chunk2_2_checked, root5Node31Step1Chunk2_3_checked, root5Node31Step1Chunk2_4_checked, root5Node31Step1Chunk2_5_checked, root5Node31Step1Chunk3_0_checked, root5Node31Step1Chunk3_1_checked, root5Node31Step1Chunk3_2_checked, root5Node31Step1Chunk3_3_checked, root5Node31Step1Chunk3_4_checked, root5Node31Step1Chunk3_5_checked, root5Node31Step1Chunk4_0_checked, root5Node31Step1Chunk4_1_checked, root5Node31Step1Chunk4_2_checked, root5Node31Step1Chunk4_3_checked, root5Node31Step1Chunk4_4_checked, root5Node31Step1Chunk4_5_checked, root5Node31Step1Chunk5_0_checked, root5Node31Step1Chunk5_1_checked, root5Node31Step1Chunk5_2_checked, root5Node31Step1Chunk5_3_checked, root5Node31Step1Chunk5_4_checked, root5Node31Step1Chunk5_5_checked, root5Node31Step1Chunk6_0_checked, root5Node31Step1Chunk6_1_checked, root5Node31Step1Chunk6_2_checked, root5Node31Step1Chunk6_3_checked, root5Node31Step1Chunk6_4_checked, root5Node31Step1Chunk6_5_checked, root5Node31Step1Chunk7_0_checked, root5Node31Step1Chunk7_1_checked, root5Node31Step1Chunk7_2_checked, root5Node31Step1Chunk7_3_checked, root5Node31Step1Chunk7_4_checked, root5Node31Step1Chunk7_5_checked, root5Node31Step1Chunk8_0_checked, root5Node31Step1Chunk8_1_checked, root5Node31Step1Chunk8_2_checked, root5Node31Step1Chunk8_3_checked, root5Node31Step1Chunk8_4_checked, root5Node31Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node31Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node31Domains1 (.output 14) = true := by decide
def root5Node32Domains0 : Domains 37 State := restrict root5Node30Domains3 15 (8,0)
def root5Node32Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(2,0)]
  | 8 => some [(7,3)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node32Domains0_fast_eq : root5Node32Domains0 = expandDomains root5Node32Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node32Domains0 v = expandDomains root5Node32Domains0Fast v from by decide) v
def root5Node32Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(2,0)]
  | 8 => [(7,3)]
  | 9 => [(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(3,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0)]
  | 21 => [(7,1)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(0,3)]
  | 29 => [(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,3)]
  | 34 => [(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node32Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(2,0)]
  | 8 => some [(7,3)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(0,3)]
  | 29 => some [(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,3)]
  | 34 => some [(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node32Domains1_fast_eq : root5Node32Domains1 = expandDomains root5Node32Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node32Domains1 v = expandDomains root5Node32Domains1Fast v from by decide) v
theorem root5Node32Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1_checked :
    checkReplacement table23 root5Node32Domains0 root5Node32Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node32Step1Chunk0_0_checked, root5Node32Step1Chunk0_1_checked, root5Node32Step1Chunk0_2_checked, root5Node32Step1Chunk0_3_checked, root5Node32Step1Chunk0_4_checked, root5Node32Step1Chunk0_5_checked, root5Node32Step1Chunk1_0_checked, root5Node32Step1Chunk1_1_checked, root5Node32Step1Chunk1_2_checked, root5Node32Step1Chunk1_3_checked, root5Node32Step1Chunk1_4_checked, root5Node32Step1Chunk1_5_checked, root5Node32Step1Chunk2_0_checked, root5Node32Step1Chunk2_1_checked, root5Node32Step1Chunk2_2_checked, root5Node32Step1Chunk2_3_checked, root5Node32Step1Chunk2_4_checked, root5Node32Step1Chunk2_5_checked, root5Node32Step1Chunk3_0_checked, root5Node32Step1Chunk3_1_checked, root5Node32Step1Chunk3_2_checked, root5Node32Step1Chunk3_3_checked, root5Node32Step1Chunk3_4_checked, root5Node32Step1Chunk3_5_checked, root5Node32Step1Chunk4_0_checked, root5Node32Step1Chunk4_1_checked, root5Node32Step1Chunk4_2_checked, root5Node32Step1Chunk4_3_checked, root5Node32Step1Chunk4_4_checked, root5Node32Step1Chunk4_5_checked, root5Node32Step1Chunk5_0_checked, root5Node32Step1Chunk5_1_checked, root5Node32Step1Chunk5_2_checked, root5Node32Step1Chunk5_3_checked, root5Node32Step1Chunk5_4_checked, root5Node32Step1Chunk5_5_checked, root5Node32Step1Chunk6_0_checked, root5Node32Step1Chunk6_1_checked, root5Node32Step1Chunk6_2_checked, root5Node32Step1Chunk6_3_checked, root5Node32Step1Chunk6_4_checked, root5Node32Step1Chunk6_5_checked, root5Node32Step1Chunk7_0_checked, root5Node32Step1Chunk7_1_checked, root5Node32Step1Chunk7_2_checked, root5Node32Step1Chunk7_3_checked, root5Node32Step1Chunk7_4_checked, root5Node32Step1Chunk7_5_checked, root5Node32Step1Chunk8_0_checked, root5Node32Step1Chunk8_1_checked, root5Node32Step1Chunk8_2_checked, root5Node32Step1Chunk8_3_checked, root5Node32Step1Chunk8_4_checked, root5Node32Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
