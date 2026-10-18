module

public import SpectreFinite.RadiusThreeRoot0Part6
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable0
public import SpectreFinite.RadiusThreeTable26
public import SpectreFinite.RadiusThreeTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node9Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(2,0),(2,2),(2,4),(4,4),(7,4),(8,4)]
  | 3 => [(0,0),(1,3),(3,3),(7,3)]
  | 4 => [(4,1),(7,5),(8,5)]
  | 5 => [(0,2),(1,0),(6,0)]
  | 6 => [(1,1),(3,1),(7,1)]
  | 7 => [(0,1),(1,5),(6,5)]
  | 8 => [(0,4),(6,1),(6,2)]
  | 9 => [(1,3)]
  | 10 => [(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3),(8,3)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(6,3)]
  | 22 => [(7,0)]
  | 23 => [(4,3)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1)]
  | 27 => [(0,2)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(6,0)]
  | 34 => [(3,1)]
  | 35 => [(0,1)]
  | _ => [(6,2)]
def root0Node9Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(7,4)]
  | 1 => some [(0,5),(6,2),(6,3)]
  | 2 => some [(2,0),(2,2),(2,4),(4,4),(7,4),(8,4)]
  | 3 => some [(0,0),(1,3),(3,3),(7,3)]
  | 4 => some [(4,1),(7,5),(8,5)]
  | 5 => some [(0,2),(1,0),(6,0)]
  | 6 => some [(1,1),(3,1),(7,1)]
  | 7 => some [(0,1),(1,5),(6,5)]
  | 8 => some [(0,4),(6,1),(6,2)]
  | 9 => some [(1,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(6,3)]
  | 22 => some [(7,0)]
  | 23 => some [(4,3)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1)]
  | 27 => some [(0,2)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1)]
  | 35 => some [(0,1)]
  | _ => some [(6,2)]
theorem root0Node9Domains2_fast_eq : root0Node9Domains2 = expandDomains root0Node9Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node9Domains2 v = expandDomains root0Node9Domains2Fast v from by decide) v
theorem root0Node9Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2_checked :
    checkReplacement table26 root0Node9Domains1 root0Node9Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node9Step2Chunk0_0_checked, root0Node9Step2Chunk0_1_checked, root0Node9Step2Chunk0_2_checked, root0Node9Step2Chunk0_3_checked, root0Node9Step2Chunk0_4_checked, root0Node9Step2Chunk0_5_checked, root0Node9Step2Chunk1_0_checked, root0Node9Step2Chunk1_1_checked, root0Node9Step2Chunk1_2_checked, root0Node9Step2Chunk1_3_checked, root0Node9Step2Chunk1_4_checked, root0Node9Step2Chunk1_5_checked, root0Node9Step2Chunk2_0_checked, root0Node9Step2Chunk2_1_checked, root0Node9Step2Chunk2_2_checked, root0Node9Step2Chunk2_3_checked, root0Node9Step2Chunk2_4_checked, root0Node9Step2Chunk2_5_checked, root0Node9Step2Chunk3_0_checked, root0Node9Step2Chunk3_1_checked, root0Node9Step2Chunk3_2_checked, root0Node9Step2Chunk3_3_checked, root0Node9Step2Chunk3_4_checked, root0Node9Step2Chunk3_5_checked, root0Node9Step2Chunk4_0_checked, root0Node9Step2Chunk4_1_checked, root0Node9Step2Chunk4_2_checked, root0Node9Step2Chunk4_3_checked, root0Node9Step2Chunk4_4_checked, root0Node9Step2Chunk4_5_checked, root0Node9Step2Chunk5_0_checked, root0Node9Step2Chunk5_1_checked, root0Node9Step2Chunk5_2_checked, root0Node9Step2Chunk5_3_checked, root0Node9Step2Chunk5_4_checked, root0Node9Step2Chunk5_5_checked, root0Node9Step2Chunk6_0_checked, root0Node9Step2Chunk6_1_checked, root0Node9Step2Chunk6_2_checked, root0Node9Step2Chunk6_3_checked, root0Node9Step2Chunk6_4_checked, root0Node9Step2Chunk6_5_checked, root0Node9Step2Chunk7_0_checked, root0Node9Step2Chunk7_1_checked, root0Node9Step2Chunk7_2_checked, root0Node9Step2Chunk7_3_checked, root0Node9Step2Chunk7_4_checked, root0Node9Step2Chunk7_5_checked, root0Node9Step2Chunk8_0_checked, root0Node9Step2Chunk8_1_checked, root0Node9Step2Chunk8_2_checked, root0Node9Step2Chunk8_3_checked, root0Node9Step2Chunk8_4_checked, root0Node9Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node9Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(7,4),(8,4)]
  | 3 => [(0,0),(1,3)]
  | 4 => [(7,5),(8,5)]
  | 5 => [(1,0),(6,0)]
  | 6 => [(7,1)]
  | 7 => [(1,5),(6,5)]
  | 8 => [(0,4),(6,1)]
  | 9 => [(1,3)]
  | 10 => [(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3),(8,3)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(6,3)]
  | 22 => [(7,0)]
  | 23 => [(4,3)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1)]
  | 27 => [(0,2)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(6,0)]
  | 34 => [(3,1)]
  | 35 => [(0,1)]
  | _ => [(6,2)]
def root0Node9Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(7,4),(8,4)]
  | 3 => some [(0,0),(1,3)]
  | 4 => some [(7,5),(8,5)]
  | 5 => some [(1,0),(6,0)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5),(6,5)]
  | 8 => some [(0,4),(6,1)]
  | 9 => some [(1,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(6,3)]
  | 22 => some [(7,0)]
  | 23 => some [(4,3)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1)]
  | 27 => some [(0,2)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1)]
  | 35 => some [(0,1)]
  | _ => some [(6,2)]
theorem root0Node9Domains3_fast_eq : root0Node9Domains3 = expandDomains root0Node9Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node9Domains3 v = expandDomains root0Node9Domains3Fast v from by decide) v
theorem root0Node9Step3Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root0Node9Domains2 root0Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains2 root0Node9Domains3
    root0Node9Domains2Fast root0Node9Domains3Fast
    root0Node9Domains2_fast_eq root0Node9Domains3_fast_eq (by decide)
theorem root0Node9Step3_checked :
    checkReplacement table6 root0Node9Domains2 root0Node9Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node9Step3Chunk0_0_checked, root0Node9Step3Chunk0_1_checked, root0Node9Step3Chunk0_2_checked, root0Node9Step3Chunk0_3_checked, root0Node9Step3Chunk0_4_checked, root0Node9Step3Chunk0_5_checked, root0Node9Step3Chunk1_0_checked, root0Node9Step3Chunk1_1_checked, root0Node9Step3Chunk1_2_checked, root0Node9Step3Chunk1_3_checked, root0Node9Step3Chunk1_4_checked, root0Node9Step3Chunk1_5_checked, root0Node9Step3Chunk2_0_checked, root0Node9Step3Chunk2_1_checked, root0Node9Step3Chunk2_2_checked, root0Node9Step3Chunk2_3_checked, root0Node9Step3Chunk2_4_checked, root0Node9Step3Chunk2_5_checked, root0Node9Step3Chunk3_0_checked, root0Node9Step3Chunk3_1_checked, root0Node9Step3Chunk3_2_checked, root0Node9Step3Chunk3_3_checked, root0Node9Step3Chunk3_4_checked, root0Node9Step3Chunk3_5_checked, root0Node9Step3Chunk4_0_checked, root0Node9Step3Chunk4_1_checked, root0Node9Step3Chunk4_2_checked, root0Node9Step3Chunk4_3_checked, root0Node9Step3Chunk4_4_checked, root0Node9Step3Chunk4_5_checked, root0Node9Step3Chunk5_0_checked, root0Node9Step3Chunk5_1_checked, root0Node9Step3Chunk5_2_checked, root0Node9Step3Chunk5_3_checked, root0Node9Step3Chunk5_4_checked, root0Node9Step3Chunk5_5_checked, root0Node9Step3Chunk6_0_checked, root0Node9Step3Chunk6_1_checked, root0Node9Step3Chunk6_2_checked, root0Node9Step3Chunk6_3_checked, root0Node9Step3Chunk6_4_checked, root0Node9Step3Chunk6_5_checked, root0Node9Step3Chunk7_0_checked, root0Node9Step3Chunk7_1_checked, root0Node9Step3Chunk7_2_checked, root0Node9Step3Chunk7_3_checked, root0Node9Step3Chunk7_4_checked, root0Node9Step3Chunk7_5_checked, root0Node9Step3Chunk8_0_checked, root0Node9Step3Chunk8_1_checked, root0Node9Step3Chunk8_2_checked, root0Node9Step3Chunk8_3_checked, root0Node9Step3Chunk8_4_checked, root0Node9Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node10Domains0 : Domains 37 State := restrict root0Node9Domains3 0 (0,1)
def root0Node10Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(7,4),(8,4)]
  | 3 => some [(0,0),(1,3)]
  | 4 => some [(7,5),(8,5)]
  | 5 => some [(1,0),(6,0)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5),(6,5)]
  | 8 => some [(0,4),(6,1)]
  | 9 => some [(1,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(6,3)]
  | 22 => some [(7,0)]
  | 23 => some [(4,3)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1)]
  | 27 => some [(0,2)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1)]
  | 35 => some [(0,1)]
  | _ => some [(6,2)]
theorem root0Node10Domains0_fast_eq : root0Node10Domains0 = expandDomains root0Node10Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node10Domains0 v = expandDomains root0Node10Domains0Fast v from by decide) v
def root0Node10Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(7,4),(8,4)]
  | 3 => [(0,0),(1,3)]
  | 4 => [(8,5)]
  | 5 => [(1,0)]
  | 6 => [(7,1)]
  | 7 => [(1,5),(6,5)]
  | 8 => [(0,4),(6,1)]
  | 9 => [(1,3)]
  | 10 => [(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3),(8,3)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(6,3)]
  | 22 => [(7,0)]
  | 23 => [(4,3)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1)]
  | 27 => [(0,2)]
  | 28 => [(1,4)]
  | 29 => [(0,5)]
  | 30 => [(2,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(6,0)]
  | 34 => [(3,1)]
  | 35 => [(0,1)]
  | _ => [(6,2)]
def root0Node10Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(7,4),(8,4)]
  | 3 => some [(0,0),(1,3)]
  | 4 => some [(8,5)]
  | 5 => some [(1,0)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5),(6,5)]
  | 8 => some [(0,4),(6,1)]
  | 9 => some [(1,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(6,3)]
  | 22 => some [(7,0)]
  | 23 => some [(4,3)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1)]
  | 27 => some [(0,2)]
  | 28 => some [(1,4)]
  | 29 => some [(0,5)]
  | 30 => some [(2,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1)]
  | 35 => some [(0,1)]
  | _ => some [(6,2)]
theorem root0Node10Domains1_fast_eq : root0Node10Domains1 = expandDomains root0Node10Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node10Domains1 v = expandDomains root0Node10Domains1Fast v from by decide) v
theorem root0Node10Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1_checked :
    checkReplacement table0 root0Node10Domains0 root0Node10Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node10Step1Chunk0_0_checked, root0Node10Step1Chunk0_1_checked, root0Node10Step1Chunk0_2_checked, root0Node10Step1Chunk0_3_checked, root0Node10Step1Chunk0_4_checked, root0Node10Step1Chunk0_5_checked, root0Node10Step1Chunk1_0_checked, root0Node10Step1Chunk1_1_checked, root0Node10Step1Chunk1_2_checked, root0Node10Step1Chunk1_3_checked, root0Node10Step1Chunk1_4_checked, root0Node10Step1Chunk1_5_checked, root0Node10Step1Chunk2_0_checked, root0Node10Step1Chunk2_1_checked, root0Node10Step1Chunk2_2_checked, root0Node10Step1Chunk2_3_checked, root0Node10Step1Chunk2_4_checked, root0Node10Step1Chunk2_5_checked, root0Node10Step1Chunk3_0_checked, root0Node10Step1Chunk3_1_checked, root0Node10Step1Chunk3_2_checked, root0Node10Step1Chunk3_3_checked, root0Node10Step1Chunk3_4_checked, root0Node10Step1Chunk3_5_checked, root0Node10Step1Chunk4_0_checked, root0Node10Step1Chunk4_1_checked, root0Node10Step1Chunk4_2_checked, root0Node10Step1Chunk4_3_checked, root0Node10Step1Chunk4_4_checked, root0Node10Step1Chunk4_5_checked, root0Node10Step1Chunk5_0_checked, root0Node10Step1Chunk5_1_checked, root0Node10Step1Chunk5_2_checked, root0Node10Step1Chunk5_3_checked, root0Node10Step1Chunk5_4_checked, root0Node10Step1Chunk5_5_checked, root0Node10Step1Chunk6_0_checked, root0Node10Step1Chunk6_1_checked, root0Node10Step1Chunk6_2_checked, root0Node10Step1Chunk6_3_checked, root0Node10Step1Chunk6_4_checked, root0Node10Step1Chunk6_5_checked, root0Node10Step1Chunk7_0_checked, root0Node10Step1Chunk7_1_checked, root0Node10Step1Chunk7_2_checked, root0Node10Step1Chunk7_3_checked, root0Node10Step1Chunk7_4_checked, root0Node10Step1Chunk7_5_checked, root0Node10Step1Chunk8_0_checked, root0Node10Step1Chunk8_1_checked, root0Node10Step1Chunk8_2_checked, root0Node10Step1Chunk8_3_checked, root0Node10Step1Chunk8_4_checked, root0Node10Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
