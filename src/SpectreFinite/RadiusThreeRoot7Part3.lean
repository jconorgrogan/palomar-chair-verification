module

public import SpectreFinite.RadiusThreeRoot7Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable2
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node2Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(5,5)]
  | 1 => [(1,0),(3,0)]
  | 2 => [(2,1),(2,5)]
  | 3 => [(0,2),(6,0)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(0,0)]
  | 7 => [(3,2),(7,2)]
  | 8 => [(4,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1),(6,5)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0),(7,0)]
  | 22 => [(5,4),(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,5)]
  | _ => [(7,0),(8,0)]
def root7Node2Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,5)]
  | 1 => some [(1,0),(3,0)]
  | 2 => some [(2,1),(2,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(0,0)]
  | 7 => some [(3,2),(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1),(6,5)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0),(7,0)]
  | 22 => some [(5,4),(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,5)]
  | _ => some [(7,0),(8,0)]
theorem root7Node2Domains3_fast_eq : root7Node2Domains3 = expandDomains root7Node2Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node2Domains3 v = expandDomains root7Node2Domains3Fast v from by decide) v
theorem root7Node2Step3Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3_checked :
    checkReplacement table2 root7Node2Domains2 root7Node2Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node2Step3Chunk0_0_checked, root7Node2Step3Chunk0_1_checked, root7Node2Step3Chunk0_2_checked, root7Node2Step3Chunk0_3_checked, root7Node2Step3Chunk0_4_checked, root7Node2Step3Chunk0_5_checked, root7Node2Step3Chunk1_0_checked, root7Node2Step3Chunk1_1_checked, root7Node2Step3Chunk1_2_checked, root7Node2Step3Chunk1_3_checked, root7Node2Step3Chunk1_4_checked, root7Node2Step3Chunk1_5_checked, root7Node2Step3Chunk2_0_checked, root7Node2Step3Chunk2_1_checked, root7Node2Step3Chunk2_2_checked, root7Node2Step3Chunk2_3_checked, root7Node2Step3Chunk2_4_checked, root7Node2Step3Chunk2_5_checked, root7Node2Step3Chunk3_0_checked, root7Node2Step3Chunk3_1_checked, root7Node2Step3Chunk3_2_checked, root7Node2Step3Chunk3_3_checked, root7Node2Step3Chunk3_4_checked, root7Node2Step3Chunk3_5_checked, root7Node2Step3Chunk4_0_checked, root7Node2Step3Chunk4_1_checked, root7Node2Step3Chunk4_2_checked, root7Node2Step3Chunk4_3_checked, root7Node2Step3Chunk4_4_checked, root7Node2Step3Chunk4_5_checked, root7Node2Step3Chunk5_0_checked, root7Node2Step3Chunk5_1_checked, root7Node2Step3Chunk5_2_checked, root7Node2Step3Chunk5_3_checked, root7Node2Step3Chunk5_4_checked, root7Node2Step3Chunk5_5_checked, root7Node2Step3Chunk6_0_checked, root7Node2Step3Chunk6_1_checked, root7Node2Step3Chunk6_2_checked, root7Node2Step3Chunk6_3_checked, root7Node2Step3Chunk6_4_checked, root7Node2Step3Chunk6_5_checked, root7Node2Step3Chunk7_0_checked, root7Node2Step3Chunk7_1_checked, root7Node2Step3Chunk7_2_checked, root7Node2Step3Chunk7_3_checked, root7Node2Step3Chunk7_4_checked, root7Node2Step3Chunk7_5_checked, root7Node2Step3Chunk8_0_checked, root7Node2Step3Chunk8_1_checked, root7Node2Step3Chunk8_2_checked, root7Node2Step3Chunk8_3_checked, root7Node2Step3Chunk8_4_checked, root7Node2Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node2Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(5,5)]
  | 1 => [(1,0),(3,0)]
  | 2 => [(2,1),(2,5)]
  | 3 => [(0,2),(6,0)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(0,0)]
  | 7 => [(3,2),(7,2)]
  | 8 => [(4,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(5,4),(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,5)]
  | _ => [(7,0),(8,0)]
def root7Node2Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,5)]
  | 1 => some [(1,0),(3,0)]
  | 2 => some [(2,1),(2,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(0,0)]
  | 7 => some [(3,2),(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(5,4),(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,5)]
  | _ => some [(7,0),(8,0)]
theorem root7Node2Domains4_fast_eq : root7Node2Domains4 = expandDomains root7Node2Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node2Domains4 v = expandDomains root7Node2Domains4Fast v from by decide) v
theorem root7Node2Step4Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root7Node2Domains3 root7Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains3 root7Node2Domains4
    root7Node2Domains3Fast root7Node2Domains4Fast
    root7Node2Domains3_fast_eq root7Node2Domains4_fast_eq (by decide)
theorem root7Node2Step4_checked :
    checkReplacement table8 root7Node2Domains3 root7Node2Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node2Step4Chunk0_0_checked, root7Node2Step4Chunk0_1_checked, root7Node2Step4Chunk0_2_checked, root7Node2Step4Chunk0_3_checked, root7Node2Step4Chunk0_4_checked, root7Node2Step4Chunk0_5_checked, root7Node2Step4Chunk1_0_checked, root7Node2Step4Chunk1_1_checked, root7Node2Step4Chunk1_2_checked, root7Node2Step4Chunk1_3_checked, root7Node2Step4Chunk1_4_checked, root7Node2Step4Chunk1_5_checked, root7Node2Step4Chunk2_0_checked, root7Node2Step4Chunk2_1_checked, root7Node2Step4Chunk2_2_checked, root7Node2Step4Chunk2_3_checked, root7Node2Step4Chunk2_4_checked, root7Node2Step4Chunk2_5_checked, root7Node2Step4Chunk3_0_checked, root7Node2Step4Chunk3_1_checked, root7Node2Step4Chunk3_2_checked, root7Node2Step4Chunk3_3_checked, root7Node2Step4Chunk3_4_checked, root7Node2Step4Chunk3_5_checked, root7Node2Step4Chunk4_0_checked, root7Node2Step4Chunk4_1_checked, root7Node2Step4Chunk4_2_checked, root7Node2Step4Chunk4_3_checked, root7Node2Step4Chunk4_4_checked, root7Node2Step4Chunk4_5_checked, root7Node2Step4Chunk5_0_checked, root7Node2Step4Chunk5_1_checked, root7Node2Step4Chunk5_2_checked, root7Node2Step4Chunk5_3_checked, root7Node2Step4Chunk5_4_checked, root7Node2Step4Chunk5_5_checked, root7Node2Step4Chunk6_0_checked, root7Node2Step4Chunk6_1_checked, root7Node2Step4Chunk6_2_checked, root7Node2Step4Chunk6_3_checked, root7Node2Step4Chunk6_4_checked, root7Node2Step4Chunk6_5_checked, root7Node2Step4Chunk7_0_checked, root7Node2Step4Chunk7_1_checked, root7Node2Step4Chunk7_2_checked, root7Node2Step4Chunk7_3_checked, root7Node2Step4Chunk7_4_checked, root7Node2Step4Chunk7_5_checked, root7Node2Step4Chunk8_0_checked, root7Node2Step4Chunk8_1_checked, root7Node2Step4Chunk8_2_checked, root7Node2Step4Chunk8_3_checked, root7Node2Step4Chunk8_4_checked, root7Node2Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node2Domains5 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(5,5)]
  | 1 => [(1,0),(3,0)]
  | 2 => [(2,1),(2,5)]
  | 3 => [(0,2),(6,0)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(0,0)]
  | 7 => [(3,2),(7,2)]
  | 8 => [(4,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(5,4),(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(2,0),(7,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,5)]
  | _ => [(7,0),(8,0)]
def root7Node2Domains5Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,5)]
  | 1 => some [(1,0),(3,0)]
  | 2 => some [(2,1),(2,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(0,0)]
  | 7 => some [(3,2),(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(5,4),(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(2,0),(7,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,5)]
  | _ => some [(7,0),(8,0)]
theorem root7Node2Domains5_fast_eq : root7Node2Domains5 = expandDomains root7Node2Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node2Domains5 v = expandDomains root7Node2Domains5Fast v from by decide) v
theorem root7Node2Step5Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root7Node2Domains4 root7Node2Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains4 root7Node2Domains5
    root7Node2Domains4Fast root7Node2Domains5Fast
    root7Node2Domains4_fast_eq root7Node2Domains5_fast_eq (by decide)
theorem root7Node2Step5_checked :
    checkReplacement table22 root7Node2Domains4 root7Node2Domains5 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node2Step5Chunk0_0_checked, root7Node2Step5Chunk0_1_checked, root7Node2Step5Chunk0_2_checked, root7Node2Step5Chunk0_3_checked, root7Node2Step5Chunk0_4_checked, root7Node2Step5Chunk0_5_checked, root7Node2Step5Chunk1_0_checked, root7Node2Step5Chunk1_1_checked, root7Node2Step5Chunk1_2_checked, root7Node2Step5Chunk1_3_checked, root7Node2Step5Chunk1_4_checked, root7Node2Step5Chunk1_5_checked, root7Node2Step5Chunk2_0_checked, root7Node2Step5Chunk2_1_checked, root7Node2Step5Chunk2_2_checked, root7Node2Step5Chunk2_3_checked, root7Node2Step5Chunk2_4_checked, root7Node2Step5Chunk2_5_checked, root7Node2Step5Chunk3_0_checked, root7Node2Step5Chunk3_1_checked, root7Node2Step5Chunk3_2_checked, root7Node2Step5Chunk3_3_checked, root7Node2Step5Chunk3_4_checked, root7Node2Step5Chunk3_5_checked, root7Node2Step5Chunk4_0_checked, root7Node2Step5Chunk4_1_checked, root7Node2Step5Chunk4_2_checked, root7Node2Step5Chunk4_3_checked, root7Node2Step5Chunk4_4_checked, root7Node2Step5Chunk4_5_checked, root7Node2Step5Chunk5_0_checked, root7Node2Step5Chunk5_1_checked, root7Node2Step5Chunk5_2_checked, root7Node2Step5Chunk5_3_checked, root7Node2Step5Chunk5_4_checked, root7Node2Step5Chunk5_5_checked, root7Node2Step5Chunk6_0_checked, root7Node2Step5Chunk6_1_checked, root7Node2Step5Chunk6_2_checked, root7Node2Step5Chunk6_3_checked, root7Node2Step5Chunk6_4_checked, root7Node2Step5Chunk6_5_checked, root7Node2Step5Chunk7_0_checked, root7Node2Step5Chunk7_1_checked, root7Node2Step5Chunk7_2_checked, root7Node2Step5Chunk7_3_checked, root7Node2Step5Chunk7_4_checked, root7Node2Step5Chunk7_5_checked, root7Node2Step5Chunk8_0_checked, root7Node2Step5Chunk8_1_checked, root7Node2Step5Chunk8_2_checked, root7Node2Step5Chunk8_3_checked, root7Node2Step5Chunk8_4_checked, root7Node2Step5Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
