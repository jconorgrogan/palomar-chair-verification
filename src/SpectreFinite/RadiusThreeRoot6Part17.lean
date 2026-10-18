module

public import SpectreFinite.RadiusThreeRoot6Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable17
public import SpectreFinite.RadiusThreeTable23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node31Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(6,5)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(1,0),(3,0),(7,0)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0),(1,4),(6,4)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(0,3),(6,0),(6,1)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0),(8,0)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(7,0),(8,2)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0),(6,4)]
  | 32 => [(1,2),(7,2)]
  | 33 => [(0,3),(1,0)]
  | 34 => [(7,1),(8,1)]
  | 35 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root6Node31Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(1,0),(3,0),(7,0)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0),(6,4)]
  | 32 => some [(1,2),(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root6Node31Domains3_fast_eq : root6Node31Domains3 = expandDomains root6Node31Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node31Domains3 v = expandDomains root6Node31Domains3Fast v from by decide) v
theorem root6Node31Step3Chunk0_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_0⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk0_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_1⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk0_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_2⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk0_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_3⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk0_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_4⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk0_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_5⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk1_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_0⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk1_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_1⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk1_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_2⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk1_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_3⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk1_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_4⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk1_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_5⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk2_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_0⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk2_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_1⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk2_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_2⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk2_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_3⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk2_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_4⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk2_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_5⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk3_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_0⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk3_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_1⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk3_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_2⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk3_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_3⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk3_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_4⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk3_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_5⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk4_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_0⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk4_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_1⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk4_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_2⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk4_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_3⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk4_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_4⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk4_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_5⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk5_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_0⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk5_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_1⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk5_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_2⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk5_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_3⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk5_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_4⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk5_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_5⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk6_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_0⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk6_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_1⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk6_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_2⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk6_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_3⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk6_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_4⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk6_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_5⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk7_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_0⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk7_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_1⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk7_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_2⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk7_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_3⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk7_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_4⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk7_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_5⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk8_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_0⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk8_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_1⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk8_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_2⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk8_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_3⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk8_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_4⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3Chunk8_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_5⟩
      root6Node31Domains2 root6Node31Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains2 root6Node31Domains3
    root6Node31Domains2Fast root6Node31Domains3Fast
    root6Node31Domains2_fast_eq root6Node31Domains3_fast_eq (by decide)
theorem root6Node31Step3_checked :
    checkReplacement table17 root6Node31Domains2 root6Node31Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node31Step3Chunk0_0_checked, root6Node31Step3Chunk0_1_checked, root6Node31Step3Chunk0_2_checked, root6Node31Step3Chunk0_3_checked, root6Node31Step3Chunk0_4_checked, root6Node31Step3Chunk0_5_checked, root6Node31Step3Chunk1_0_checked, root6Node31Step3Chunk1_1_checked, root6Node31Step3Chunk1_2_checked, root6Node31Step3Chunk1_3_checked, root6Node31Step3Chunk1_4_checked, root6Node31Step3Chunk1_5_checked, root6Node31Step3Chunk2_0_checked, root6Node31Step3Chunk2_1_checked, root6Node31Step3Chunk2_2_checked, root6Node31Step3Chunk2_3_checked, root6Node31Step3Chunk2_4_checked, root6Node31Step3Chunk2_5_checked, root6Node31Step3Chunk3_0_checked, root6Node31Step3Chunk3_1_checked, root6Node31Step3Chunk3_2_checked, root6Node31Step3Chunk3_3_checked, root6Node31Step3Chunk3_4_checked, root6Node31Step3Chunk3_5_checked, root6Node31Step3Chunk4_0_checked, root6Node31Step3Chunk4_1_checked, root6Node31Step3Chunk4_2_checked, root6Node31Step3Chunk4_3_checked, root6Node31Step3Chunk4_4_checked, root6Node31Step3Chunk4_5_checked, root6Node31Step3Chunk5_0_checked, root6Node31Step3Chunk5_1_checked, root6Node31Step3Chunk5_2_checked, root6Node31Step3Chunk5_3_checked, root6Node31Step3Chunk5_4_checked, root6Node31Step3Chunk5_5_checked, root6Node31Step3Chunk6_0_checked, root6Node31Step3Chunk6_1_checked, root6Node31Step3Chunk6_2_checked, root6Node31Step3Chunk6_3_checked, root6Node31Step3Chunk6_4_checked, root6Node31Step3Chunk6_5_checked, root6Node31Step3Chunk7_0_checked, root6Node31Step3Chunk7_1_checked, root6Node31Step3Chunk7_2_checked, root6Node31Step3Chunk7_3_checked, root6Node31Step3Chunk7_4_checked, root6Node31Step3Chunk7_5_checked, root6Node31Step3Chunk8_0_checked, root6Node31Step3Chunk8_1_checked, root6Node31Step3Chunk8_2_checked, root6Node31Step3Chunk8_3_checked, root6Node31Step3Chunk8_4_checked, root6Node31Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node31Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(6,5)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(1,0),(3,0),(7,0)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0),(1,4),(6,4)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(0,3),(6,0),(6,1)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0),(8,0)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(7,0),(8,2)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0),(6,4)]
  | 32 => [(1,2),(7,2)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root6Node31Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(1,0),(3,0),(7,0)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0),(6,4)]
  | 32 => some [(1,2),(7,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root6Node31Domains4_fast_eq : root6Node31Domains4 = expandDomains root6Node31Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node31Domains4 v = expandDomains root6Node31Domains4Fast v from by decide) v
theorem root6Node31Step4Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node31Domains3 root6Node31Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains3 root6Node31Domains4
    root6Node31Domains3Fast root6Node31Domains4Fast
    root6Node31Domains3_fast_eq root6Node31Domains4_fast_eq (by decide)
theorem root6Node31Step4_checked :
    checkReplacement table23 root6Node31Domains3 root6Node31Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node31Step4Chunk0_0_checked, root6Node31Step4Chunk0_1_checked, root6Node31Step4Chunk0_2_checked, root6Node31Step4Chunk0_3_checked, root6Node31Step4Chunk0_4_checked, root6Node31Step4Chunk0_5_checked, root6Node31Step4Chunk1_0_checked, root6Node31Step4Chunk1_1_checked, root6Node31Step4Chunk1_2_checked, root6Node31Step4Chunk1_3_checked, root6Node31Step4Chunk1_4_checked, root6Node31Step4Chunk1_5_checked, root6Node31Step4Chunk2_0_checked, root6Node31Step4Chunk2_1_checked, root6Node31Step4Chunk2_2_checked, root6Node31Step4Chunk2_3_checked, root6Node31Step4Chunk2_4_checked, root6Node31Step4Chunk2_5_checked, root6Node31Step4Chunk3_0_checked, root6Node31Step4Chunk3_1_checked, root6Node31Step4Chunk3_2_checked, root6Node31Step4Chunk3_3_checked, root6Node31Step4Chunk3_4_checked, root6Node31Step4Chunk3_5_checked, root6Node31Step4Chunk4_0_checked, root6Node31Step4Chunk4_1_checked, root6Node31Step4Chunk4_2_checked, root6Node31Step4Chunk4_3_checked, root6Node31Step4Chunk4_4_checked, root6Node31Step4Chunk4_5_checked, root6Node31Step4Chunk5_0_checked, root6Node31Step4Chunk5_1_checked, root6Node31Step4Chunk5_2_checked, root6Node31Step4Chunk5_3_checked, root6Node31Step4Chunk5_4_checked, root6Node31Step4Chunk5_5_checked, root6Node31Step4Chunk6_0_checked, root6Node31Step4Chunk6_1_checked, root6Node31Step4Chunk6_2_checked, root6Node31Step4Chunk6_3_checked, root6Node31Step4Chunk6_4_checked, root6Node31Step4Chunk6_5_checked, root6Node31Step4Chunk7_0_checked, root6Node31Step4Chunk7_1_checked, root6Node31Step4Chunk7_2_checked, root6Node31Step4Chunk7_3_checked, root6Node31Step4Chunk7_4_checked, root6Node31Step4Chunk7_5_checked, root6Node31Step4Chunk8_0_checked, root6Node31Step4Chunk8_1_checked, root6Node31Step4Chunk8_2_checked, root6Node31Step4Chunk8_3_checked, root6Node31Step4Chunk8_4_checked, root6Node31Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node32Domains0 : Domains 37 State := restrict root6Node31Domains4 2 (5,1)
def root6Node32Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(1,0),(3,0),(7,0)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0),(6,4)]
  | 32 => some [(1,2),(7,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root6Node32Domains0_fast_eq : root6Node32Domains0 = expandDomains root6Node32Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node32Domains0 v = expandDomains root6Node32Domains0Fast v from by decide) v
def root6Node32Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(1,0)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(6,1)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0),(6,4)]
  | 32 => [(1,2),(7,2)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root6Node32Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(1,0)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0),(6,4)]
  | 32 => some [(1,2),(7,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root6Node32Domains1_fast_eq : root6Node32Domains1 = expandDomains root6Node32Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node32Domains1 v = expandDomains root6Node32Domains1Fast v from by decide) v
theorem root6Node32Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1_checked :
    checkReplacement table13 root6Node32Domains0 root6Node32Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node32Step1Chunk0_0_checked, root6Node32Step1Chunk0_1_checked, root6Node32Step1Chunk0_2_checked, root6Node32Step1Chunk0_3_checked, root6Node32Step1Chunk0_4_checked, root6Node32Step1Chunk0_5_checked, root6Node32Step1Chunk1_0_checked, root6Node32Step1Chunk1_1_checked, root6Node32Step1Chunk1_2_checked, root6Node32Step1Chunk1_3_checked, root6Node32Step1Chunk1_4_checked, root6Node32Step1Chunk1_5_checked, root6Node32Step1Chunk2_0_checked, root6Node32Step1Chunk2_1_checked, root6Node32Step1Chunk2_2_checked, root6Node32Step1Chunk2_3_checked, root6Node32Step1Chunk2_4_checked, root6Node32Step1Chunk2_5_checked, root6Node32Step1Chunk3_0_checked, root6Node32Step1Chunk3_1_checked, root6Node32Step1Chunk3_2_checked, root6Node32Step1Chunk3_3_checked, root6Node32Step1Chunk3_4_checked, root6Node32Step1Chunk3_5_checked, root6Node32Step1Chunk4_0_checked, root6Node32Step1Chunk4_1_checked, root6Node32Step1Chunk4_2_checked, root6Node32Step1Chunk4_3_checked, root6Node32Step1Chunk4_4_checked, root6Node32Step1Chunk4_5_checked, root6Node32Step1Chunk5_0_checked, root6Node32Step1Chunk5_1_checked, root6Node32Step1Chunk5_2_checked, root6Node32Step1Chunk5_3_checked, root6Node32Step1Chunk5_4_checked, root6Node32Step1Chunk5_5_checked, root6Node32Step1Chunk6_0_checked, root6Node32Step1Chunk6_1_checked, root6Node32Step1Chunk6_2_checked, root6Node32Step1Chunk6_3_checked, root6Node32Step1Chunk6_4_checked, root6Node32Step1Chunk6_5_checked, root6Node32Step1Chunk7_0_checked, root6Node32Step1Chunk7_1_checked, root6Node32Step1Chunk7_2_checked, root6Node32Step1Chunk7_3_checked, root6Node32Step1Chunk7_4_checked, root6Node32Step1Chunk7_5_checked, root6Node32Step1Chunk8_0_checked, root6Node32Step1Chunk8_1_checked, root6Node32Step1Chunk8_2_checked, root6Node32Step1Chunk8_3_checked, root6Node32Step1Chunk8_4_checked, root6Node32Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
