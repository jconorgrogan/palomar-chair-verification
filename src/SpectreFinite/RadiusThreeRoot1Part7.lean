module

public import SpectreFinite.RadiusThreeRoot1Part6
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable23
public import SpectreFinite.RadiusThreeTable25
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node9Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(0,3)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(7,4)]
  | 23 => [(1,3),(6,3)]
  | 24 => [(7,2),(8,2)]
  | 25 => [(4,0),(8,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2),(8,2)]
  | 28 => [(0,2),(6,5)]
  | 29 => [(0,4),(1,1)]
  | 30 => [(5,1),(5,4)]
  | 31 => [(0,1),(6,4)]
  | 32 => [(1,2),(6,2)]
  | 33 => [(7,0),(8,0)]
  | 34 => [(4,3),(8,3)]
  | 35 => [(3,5),(5,5),(7,5)]
  | _ => [(0,3),(1,0)]
def root1Node9Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3),(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(0,2),(6,5)]
  | 29 => some [(0,4),(1,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,1),(6,4)]
  | 32 => some [(1,2),(6,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root1Node9Domains2_fast_eq : root1Node9Domains2 = expandDomains root1Node9Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node9Domains2 v = expandDomains root1Node9Domains2Fast v from by decide) v
theorem root1Node9Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root1Node9Domains1 root1Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node9Domains1 root1Node9Domains2
    root1Node9Domains1Fast root1Node9Domains2Fast
    root1Node9Domains1_fast_eq root1Node9Domains2_fast_eq (by decide)
theorem root1Node9Step2_checked :
    checkReplacement table25 root1Node9Domains1 root1Node9Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node9Step2Chunk0_0_checked, root1Node9Step2Chunk0_1_checked, root1Node9Step2Chunk0_2_checked, root1Node9Step2Chunk0_3_checked, root1Node9Step2Chunk0_4_checked, root1Node9Step2Chunk0_5_checked, root1Node9Step2Chunk1_0_checked, root1Node9Step2Chunk1_1_checked, root1Node9Step2Chunk1_2_checked, root1Node9Step2Chunk1_3_checked, root1Node9Step2Chunk1_4_checked, root1Node9Step2Chunk1_5_checked, root1Node9Step2Chunk2_0_checked, root1Node9Step2Chunk2_1_checked, root1Node9Step2Chunk2_2_checked, root1Node9Step2Chunk2_3_checked, root1Node9Step2Chunk2_4_checked, root1Node9Step2Chunk2_5_checked, root1Node9Step2Chunk3_0_checked, root1Node9Step2Chunk3_1_checked, root1Node9Step2Chunk3_2_checked, root1Node9Step2Chunk3_3_checked, root1Node9Step2Chunk3_4_checked, root1Node9Step2Chunk3_5_checked, root1Node9Step2Chunk4_0_checked, root1Node9Step2Chunk4_1_checked, root1Node9Step2Chunk4_2_checked, root1Node9Step2Chunk4_3_checked, root1Node9Step2Chunk4_4_checked, root1Node9Step2Chunk4_5_checked, root1Node9Step2Chunk5_0_checked, root1Node9Step2Chunk5_1_checked, root1Node9Step2Chunk5_2_checked, root1Node9Step2Chunk5_3_checked, root1Node9Step2Chunk5_4_checked, root1Node9Step2Chunk5_5_checked, root1Node9Step2Chunk6_0_checked, root1Node9Step2Chunk6_1_checked, root1Node9Step2Chunk6_2_checked, root1Node9Step2Chunk6_3_checked, root1Node9Step2Chunk6_4_checked, root1Node9Step2Chunk6_5_checked, root1Node9Step2Chunk7_0_checked, root1Node9Step2Chunk7_1_checked, root1Node9Step2Chunk7_2_checked, root1Node9Step2Chunk7_3_checked, root1Node9Step2Chunk7_4_checked, root1Node9Step2Chunk7_5_checked, root1Node9Step2Chunk8_0_checked, root1Node9Step2Chunk8_1_checked, root1Node9Step2Chunk8_2_checked, root1Node9Step2Chunk8_3_checked, root1Node9Step2Chunk8_4_checked, root1Node9Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node10Domains0 : Domains 37 State := restrict root1Node9Domains2 14 (1,4)
def root1Node10Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(1,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3),(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(0,2),(6,5)]
  | 29 => some [(0,4),(1,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,1),(6,4)]
  | 32 => some [(1,2),(6,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root1Node10Domains0_fast_eq : root1Node10Domains0 = expandDomains root1Node10Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node10Domains0 v = expandDomains root1Node10Domains0Fast v from by decide) v
def root1Node10Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(0,3)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,4)]
  | 23 => [(1,3),(6,3)]
  | 24 => [(8,2)]
  | 25 => [(8,0)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(0,2),(6,5)]
  | 29 => [(0,4),(1,1)]
  | 30 => [(5,4)]
  | 31 => [(6,4)]
  | 32 => [(1,2)]
  | 33 => [(7,0),(8,0)]
  | 34 => [(4,3),(8,3)]
  | 35 => [(7,5)]
  | _ => [(0,3)]
def root1Node10Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(1,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3),(6,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(0,2),(6,5)]
  | 29 => some [(0,4),(1,1)]
  | 30 => some [(5,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root1Node10Domains1_fast_eq : root1Node10Domains1 = expandDomains root1Node10Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node10Domains1 v = expandDomains root1Node10Domains1Fast v from by decide) v
theorem root1Node10Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root1Node10Domains0 root1Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains0 root1Node10Domains1
    root1Node10Domains0Fast root1Node10Domains1Fast
    root1Node10Domains0_fast_eq root1Node10Domains1_fast_eq (by decide)
theorem root1Node10Step1_checked :
    checkReplacement table26 root1Node10Domains0 root1Node10Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node10Step1Chunk0_0_checked, root1Node10Step1Chunk0_1_checked, root1Node10Step1Chunk0_2_checked, root1Node10Step1Chunk0_3_checked, root1Node10Step1Chunk0_4_checked, root1Node10Step1Chunk0_5_checked, root1Node10Step1Chunk1_0_checked, root1Node10Step1Chunk1_1_checked, root1Node10Step1Chunk1_2_checked, root1Node10Step1Chunk1_3_checked, root1Node10Step1Chunk1_4_checked, root1Node10Step1Chunk1_5_checked, root1Node10Step1Chunk2_0_checked, root1Node10Step1Chunk2_1_checked, root1Node10Step1Chunk2_2_checked, root1Node10Step1Chunk2_3_checked, root1Node10Step1Chunk2_4_checked, root1Node10Step1Chunk2_5_checked, root1Node10Step1Chunk3_0_checked, root1Node10Step1Chunk3_1_checked, root1Node10Step1Chunk3_2_checked, root1Node10Step1Chunk3_3_checked, root1Node10Step1Chunk3_4_checked, root1Node10Step1Chunk3_5_checked, root1Node10Step1Chunk4_0_checked, root1Node10Step1Chunk4_1_checked, root1Node10Step1Chunk4_2_checked, root1Node10Step1Chunk4_3_checked, root1Node10Step1Chunk4_4_checked, root1Node10Step1Chunk4_5_checked, root1Node10Step1Chunk5_0_checked, root1Node10Step1Chunk5_1_checked, root1Node10Step1Chunk5_2_checked, root1Node10Step1Chunk5_3_checked, root1Node10Step1Chunk5_4_checked, root1Node10Step1Chunk5_5_checked, root1Node10Step1Chunk6_0_checked, root1Node10Step1Chunk6_1_checked, root1Node10Step1Chunk6_2_checked, root1Node10Step1Chunk6_3_checked, root1Node10Step1Chunk6_4_checked, root1Node10Step1Chunk6_5_checked, root1Node10Step1Chunk7_0_checked, root1Node10Step1Chunk7_1_checked, root1Node10Step1Chunk7_2_checked, root1Node10Step1Chunk7_3_checked, root1Node10Step1Chunk7_4_checked, root1Node10Step1Chunk7_5_checked, root1Node10Step1Chunk8_0_checked, root1Node10Step1Chunk8_1_checked, root1Node10Step1Chunk8_2_checked, root1Node10Step1Chunk8_3_checked, root1Node10Step1Chunk8_4_checked, root1Node10Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node10Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(0,3)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(8,2)]
  | 25 => [(8,0)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(6,5)]
  | 29 => [(0,4)]
  | 30 => [(5,4)]
  | 31 => [(6,4)]
  | 32 => [(1,2)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(7,5)]
  | _ => [(0,3)]
def root1Node10Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(1,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(6,5)]
  | 29 => some [(0,4)]
  | 30 => some [(5,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root1Node10Domains2_fast_eq : root1Node10Domains2 = expandDomains root1Node10Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node10Domains2 v = expandDomains root1Node10Domains2Fast v from by decide) v
theorem root1Node10Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root1Node10Domains1 root1Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node10Domains1 root1Node10Domains2
    root1Node10Domains1Fast root1Node10Domains2Fast
    root1Node10Domains1_fast_eq root1Node10Domains2_fast_eq (by decide)
theorem root1Node10Step2_checked :
    checkReplacement table23 root1Node10Domains1 root1Node10Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node10Step2Chunk0_0_checked, root1Node10Step2Chunk0_1_checked, root1Node10Step2Chunk0_2_checked, root1Node10Step2Chunk0_3_checked, root1Node10Step2Chunk0_4_checked, root1Node10Step2Chunk0_5_checked, root1Node10Step2Chunk1_0_checked, root1Node10Step2Chunk1_1_checked, root1Node10Step2Chunk1_2_checked, root1Node10Step2Chunk1_3_checked, root1Node10Step2Chunk1_4_checked, root1Node10Step2Chunk1_5_checked, root1Node10Step2Chunk2_0_checked, root1Node10Step2Chunk2_1_checked, root1Node10Step2Chunk2_2_checked, root1Node10Step2Chunk2_3_checked, root1Node10Step2Chunk2_4_checked, root1Node10Step2Chunk2_5_checked, root1Node10Step2Chunk3_0_checked, root1Node10Step2Chunk3_1_checked, root1Node10Step2Chunk3_2_checked, root1Node10Step2Chunk3_3_checked, root1Node10Step2Chunk3_4_checked, root1Node10Step2Chunk3_5_checked, root1Node10Step2Chunk4_0_checked, root1Node10Step2Chunk4_1_checked, root1Node10Step2Chunk4_2_checked, root1Node10Step2Chunk4_3_checked, root1Node10Step2Chunk4_4_checked, root1Node10Step2Chunk4_5_checked, root1Node10Step2Chunk5_0_checked, root1Node10Step2Chunk5_1_checked, root1Node10Step2Chunk5_2_checked, root1Node10Step2Chunk5_3_checked, root1Node10Step2Chunk5_4_checked, root1Node10Step2Chunk5_5_checked, root1Node10Step2Chunk6_0_checked, root1Node10Step2Chunk6_1_checked, root1Node10Step2Chunk6_2_checked, root1Node10Step2Chunk6_3_checked, root1Node10Step2Chunk6_4_checked, root1Node10Step2Chunk6_5_checked, root1Node10Step2Chunk7_0_checked, root1Node10Step2Chunk7_1_checked, root1Node10Step2Chunk7_2_checked, root1Node10Step2Chunk7_3_checked, root1Node10Step2Chunk7_4_checked, root1Node10Step2Chunk7_5_checked, root1Node10Step2Chunk8_0_checked, root1Node10Step2Chunk8_1_checked, root1Node10Step2Chunk8_2_checked, root1Node10Step2Chunk8_3_checked, root1Node10Step2Chunk8_4_checked, root1Node10Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node10Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node10Domains2 (.output 3) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
