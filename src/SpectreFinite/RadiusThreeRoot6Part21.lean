module

public import SpectreFinite.RadiusThreeRoot6Part20
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable23
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node38Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0),(6,4)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(4,3)]
  | 7 => [(1,5),(3,5)]
  | 8 => [(0,3),(6,1)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0),(2,4)]
  | 14 => [(1,3),(7,3)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(3,1),(7,1)]
  | 20 => [(0,1),(6,5)]
  | 21 => [(0,4),(6,2)]
  | 22 => [(4,0),(8,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(0,1),(6,4)]
  | 29 => [(1,2),(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0)]
  | 32 => [(7,2)]
  | 33 => [(0,3),(1,0)]
  | 34 => [(7,1),(8,1)]
  | 35 => [(1,5)]
  | _ => [(6,1)]
def root6Node38Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0),(6,4)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5),(3,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0),(2,4)]
  | 14 => some [(1,3),(7,3)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(6,5)]
  | 21 => some [(0,4),(6,2)]
  | 22 => some [(4,0),(8,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(0,1),(6,4)]
  | 29 => some [(1,2),(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node38Domains2_fast_eq : root6Node38Domains2 = expandDomains root6Node38Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node38Domains2 v = expandDomains root6Node38Domains2Fast v from by decide) v
theorem root6Node38Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2_checked :
    checkReplacement table26 root6Node38Domains1 root6Node38Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node38Step2Chunk0_0_checked, root6Node38Step2Chunk0_1_checked, root6Node38Step2Chunk0_2_checked, root6Node38Step2Chunk0_3_checked, root6Node38Step2Chunk0_4_checked, root6Node38Step2Chunk0_5_checked, root6Node38Step2Chunk1_0_checked, root6Node38Step2Chunk1_1_checked, root6Node38Step2Chunk1_2_checked, root6Node38Step2Chunk1_3_checked, root6Node38Step2Chunk1_4_checked, root6Node38Step2Chunk1_5_checked, root6Node38Step2Chunk2_0_checked, root6Node38Step2Chunk2_1_checked, root6Node38Step2Chunk2_2_checked, root6Node38Step2Chunk2_3_checked, root6Node38Step2Chunk2_4_checked, root6Node38Step2Chunk2_5_checked, root6Node38Step2Chunk3_0_checked, root6Node38Step2Chunk3_1_checked, root6Node38Step2Chunk3_2_checked, root6Node38Step2Chunk3_3_checked, root6Node38Step2Chunk3_4_checked, root6Node38Step2Chunk3_5_checked, root6Node38Step2Chunk4_0_checked, root6Node38Step2Chunk4_1_checked, root6Node38Step2Chunk4_2_checked, root6Node38Step2Chunk4_3_checked, root6Node38Step2Chunk4_4_checked, root6Node38Step2Chunk4_5_checked, root6Node38Step2Chunk5_0_checked, root6Node38Step2Chunk5_1_checked, root6Node38Step2Chunk5_2_checked, root6Node38Step2Chunk5_3_checked, root6Node38Step2Chunk5_4_checked, root6Node38Step2Chunk5_5_checked, root6Node38Step2Chunk6_0_checked, root6Node38Step2Chunk6_1_checked, root6Node38Step2Chunk6_2_checked, root6Node38Step2Chunk6_3_checked, root6Node38Step2Chunk6_4_checked, root6Node38Step2Chunk6_5_checked, root6Node38Step2Chunk7_0_checked, root6Node38Step2Chunk7_1_checked, root6Node38Step2Chunk7_2_checked, root6Node38Step2Chunk7_3_checked, root6Node38Step2Chunk7_4_checked, root6Node38Step2Chunk7_5_checked, root6Node38Step2Chunk8_0_checked, root6Node38Step2Chunk8_1_checked, root6Node38Step2Chunk8_2_checked, root6Node38Step2Chunk8_3_checked, root6Node38Step2Chunk8_4_checked, root6Node38Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node39Domains0 : Domains 37 State := restrict root6Node38Domains2 3 (0,0)
def root6Node39Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5),(3,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0),(2,4)]
  | 14 => some [(1,3),(7,3)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(6,5)]
  | 21 => some [(0,4),(6,2)]
  | 22 => some [(4,0),(8,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(0,1),(6,4)]
  | 29 => some [(1,2),(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node39Domains0_fast_eq : root6Node39Domains0 = expandDomains root6Node39Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node39Domains0 v = expandDomains root6Node39Domains0Fast v from by decide) v
def root6Node39Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(4,3)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(3,1)]
  | 20 => [(0,1)]
  | 21 => [(6,2)]
  | 22 => [(4,0),(8,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(1,0)]
  | 28 => [(0,1),(6,4)]
  | 29 => [(1,2),(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0)]
  | 32 => [(7,2)]
  | 33 => [(0,3),(1,0)]
  | 34 => [(7,1),(8,1)]
  | 35 => [(1,5)]
  | _ => [(6,1)]
def root6Node39Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1)]
  | 20 => some [(0,1)]
  | 21 => some [(6,2)]
  | 22 => some [(4,0),(8,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(0,1),(6,4)]
  | 29 => some [(1,2),(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node39Domains1_fast_eq : root6Node39Domains1 = expandDomains root6Node39Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node39Domains1 v = expandDomains root6Node39Domains1Fast v from by decide) v
theorem root6Node39Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1_checked :
    checkReplacement table13 root6Node39Domains0 root6Node39Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node39Step1Chunk0_0_checked, root6Node39Step1Chunk0_1_checked, root6Node39Step1Chunk0_2_checked, root6Node39Step1Chunk0_3_checked, root6Node39Step1Chunk0_4_checked, root6Node39Step1Chunk0_5_checked, root6Node39Step1Chunk1_0_checked, root6Node39Step1Chunk1_1_checked, root6Node39Step1Chunk1_2_checked, root6Node39Step1Chunk1_3_checked, root6Node39Step1Chunk1_4_checked, root6Node39Step1Chunk1_5_checked, root6Node39Step1Chunk2_0_checked, root6Node39Step1Chunk2_1_checked, root6Node39Step1Chunk2_2_checked, root6Node39Step1Chunk2_3_checked, root6Node39Step1Chunk2_4_checked, root6Node39Step1Chunk2_5_checked, root6Node39Step1Chunk3_0_checked, root6Node39Step1Chunk3_1_checked, root6Node39Step1Chunk3_2_checked, root6Node39Step1Chunk3_3_checked, root6Node39Step1Chunk3_4_checked, root6Node39Step1Chunk3_5_checked, root6Node39Step1Chunk4_0_checked, root6Node39Step1Chunk4_1_checked, root6Node39Step1Chunk4_2_checked, root6Node39Step1Chunk4_3_checked, root6Node39Step1Chunk4_4_checked, root6Node39Step1Chunk4_5_checked, root6Node39Step1Chunk5_0_checked, root6Node39Step1Chunk5_1_checked, root6Node39Step1Chunk5_2_checked, root6Node39Step1Chunk5_3_checked, root6Node39Step1Chunk5_4_checked, root6Node39Step1Chunk5_5_checked, root6Node39Step1Chunk6_0_checked, root6Node39Step1Chunk6_1_checked, root6Node39Step1Chunk6_2_checked, root6Node39Step1Chunk6_3_checked, root6Node39Step1Chunk6_4_checked, root6Node39Step1Chunk6_5_checked, root6Node39Step1Chunk7_0_checked, root6Node39Step1Chunk7_1_checked, root6Node39Step1Chunk7_2_checked, root6Node39Step1Chunk7_3_checked, root6Node39Step1Chunk7_4_checked, root6Node39Step1Chunk7_5_checked, root6Node39Step1Chunk8_0_checked, root6Node39Step1Chunk8_1_checked, root6Node39Step1Chunk8_2_checked, root6Node39Step1Chunk8_3_checked, root6Node39Step1Chunk8_4_checked, root6Node39Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node40Domains0 : Domains 37 State := restrict root6Node39Domains1 22 (4,0)
def root6Node40Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1)]
  | 20 => some [(0,1)]
  | 21 => some [(6,2)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(0,1),(6,4)]
  | 29 => some [(1,2),(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node40Domains0_fast_eq : root6Node40Domains0 = expandDomains root6Node40Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node40Domains0 v = expandDomains root6Node40Domains0Fast v from by decide) v
def root6Node40Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(4,3)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(3,1)]
  | 20 => [(0,1)]
  | 21 => [(6,2)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(1,0)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0)]
  | 32 => [(7,2)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(1,5)]
  | _ => [(6,1)]
def root6Node40Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(4,3)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1)]
  | 20 => some [(0,1)]
  | 21 => some [(6,2)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node40Domains1_fast_eq : root6Node40Domains1 = expandDomains root6Node40Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node40Domains1 v = expandDomains root6Node40Domains1Fast v from by decide) v
theorem root6Node40Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1_checked :
    checkReplacement table23 root6Node40Domains0 root6Node40Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node40Step1Chunk0_0_checked, root6Node40Step1Chunk0_1_checked, root6Node40Step1Chunk0_2_checked, root6Node40Step1Chunk0_3_checked, root6Node40Step1Chunk0_4_checked, root6Node40Step1Chunk0_5_checked, root6Node40Step1Chunk1_0_checked, root6Node40Step1Chunk1_1_checked, root6Node40Step1Chunk1_2_checked, root6Node40Step1Chunk1_3_checked, root6Node40Step1Chunk1_4_checked, root6Node40Step1Chunk1_5_checked, root6Node40Step1Chunk2_0_checked, root6Node40Step1Chunk2_1_checked, root6Node40Step1Chunk2_2_checked, root6Node40Step1Chunk2_3_checked, root6Node40Step1Chunk2_4_checked, root6Node40Step1Chunk2_5_checked, root6Node40Step1Chunk3_0_checked, root6Node40Step1Chunk3_1_checked, root6Node40Step1Chunk3_2_checked, root6Node40Step1Chunk3_3_checked, root6Node40Step1Chunk3_4_checked, root6Node40Step1Chunk3_5_checked, root6Node40Step1Chunk4_0_checked, root6Node40Step1Chunk4_1_checked, root6Node40Step1Chunk4_2_checked, root6Node40Step1Chunk4_3_checked, root6Node40Step1Chunk4_4_checked, root6Node40Step1Chunk4_5_checked, root6Node40Step1Chunk5_0_checked, root6Node40Step1Chunk5_1_checked, root6Node40Step1Chunk5_2_checked, root6Node40Step1Chunk5_3_checked, root6Node40Step1Chunk5_4_checked, root6Node40Step1Chunk5_5_checked, root6Node40Step1Chunk6_0_checked, root6Node40Step1Chunk6_1_checked, root6Node40Step1Chunk6_2_checked, root6Node40Step1Chunk6_3_checked, root6Node40Step1Chunk6_4_checked, root6Node40Step1Chunk6_5_checked, root6Node40Step1Chunk7_0_checked, root6Node40Step1Chunk7_1_checked, root6Node40Step1Chunk7_2_checked, root6Node40Step1Chunk7_3_checked, root6Node40Step1Chunk7_4_checked, root6Node40Step1Chunk7_5_checked, root6Node40Step1Chunk8_0_checked, root6Node40Step1Chunk8_1_checked, root6Node40Step1Chunk8_2_checked, root6Node40Step1Chunk8_3_checked, root6Node40Step1Chunk8_4_checked, root6Node40Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node40Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node40Domains1 (.output 19) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
