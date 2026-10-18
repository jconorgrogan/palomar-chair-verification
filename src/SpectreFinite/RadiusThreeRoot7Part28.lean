module

public import SpectreFinite.RadiusThreeRoot7Part27
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node43Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(6,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(8,1)]
  | 14 => [(6,5)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(7,0)]
  | 22 => [(5,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(6,3)]
  | 27 => [(7,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(2,0),(4,0)]
  | 34 => [(7,3)]
  | 35 => [(5,2)]
  | _ => [(8,0)]
def root7Node43Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(7,0)]
  | 22 => some [(5,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(6,3)]
  | 27 => some [(7,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(2,0),(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(5,2)]
  | _ => some [(8,0)]
theorem root7Node43Domains2_fast_eq : root7Node43Domains2 = expandDomains root7Node43Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node43Domains2 v = expandDomains root7Node43Domains2Fast v from by decide) v
theorem root7Node43Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root7Node43Domains1 root7Node43Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains1 root7Node43Domains2
    root7Node43Domains1Fast root7Node43Domains2Fast
    root7Node43Domains1_fast_eq root7Node43Domains2_fast_eq (by decide)
theorem root7Node43Step2_checked :
    checkReplacement table26 root7Node43Domains1 root7Node43Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node43Step2Chunk0_0_checked, root7Node43Step2Chunk0_1_checked, root7Node43Step2Chunk0_2_checked, root7Node43Step2Chunk0_3_checked, root7Node43Step2Chunk0_4_checked, root7Node43Step2Chunk0_5_checked, root7Node43Step2Chunk1_0_checked, root7Node43Step2Chunk1_1_checked, root7Node43Step2Chunk1_2_checked, root7Node43Step2Chunk1_3_checked, root7Node43Step2Chunk1_4_checked, root7Node43Step2Chunk1_5_checked, root7Node43Step2Chunk2_0_checked, root7Node43Step2Chunk2_1_checked, root7Node43Step2Chunk2_2_checked, root7Node43Step2Chunk2_3_checked, root7Node43Step2Chunk2_4_checked, root7Node43Step2Chunk2_5_checked, root7Node43Step2Chunk3_0_checked, root7Node43Step2Chunk3_1_checked, root7Node43Step2Chunk3_2_checked, root7Node43Step2Chunk3_3_checked, root7Node43Step2Chunk3_4_checked, root7Node43Step2Chunk3_5_checked, root7Node43Step2Chunk4_0_checked, root7Node43Step2Chunk4_1_checked, root7Node43Step2Chunk4_2_checked, root7Node43Step2Chunk4_3_checked, root7Node43Step2Chunk4_4_checked, root7Node43Step2Chunk4_5_checked, root7Node43Step2Chunk5_0_checked, root7Node43Step2Chunk5_1_checked, root7Node43Step2Chunk5_2_checked, root7Node43Step2Chunk5_3_checked, root7Node43Step2Chunk5_4_checked, root7Node43Step2Chunk5_5_checked, root7Node43Step2Chunk6_0_checked, root7Node43Step2Chunk6_1_checked, root7Node43Step2Chunk6_2_checked, root7Node43Step2Chunk6_3_checked, root7Node43Step2Chunk6_4_checked, root7Node43Step2Chunk6_5_checked, root7Node43Step2Chunk7_0_checked, root7Node43Step2Chunk7_1_checked, root7Node43Step2Chunk7_2_checked, root7Node43Step2Chunk7_3_checked, root7Node43Step2Chunk7_4_checked, root7Node43Step2Chunk7_5_checked, root7Node43Step2Chunk8_0_checked, root7Node43Step2Chunk8_1_checked, root7Node43Step2Chunk8_2_checked, root7Node43Step2Chunk8_3_checked, root7Node43Step2Chunk8_4_checked, root7Node43Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node43Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(6,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(8,1)]
  | 14 => [(6,5)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(7,0)]
  | 22 => [(5,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(6,3)]
  | 27 => [(7,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(2,0)]
  | 34 => [(7,3)]
  | 35 => [(5,2)]
  | _ => [(8,0)]
def root7Node43Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(7,0)]
  | 22 => some [(5,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(6,3)]
  | 27 => some [(7,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(2,0)]
  | 34 => some [(7,3)]
  | 35 => some [(5,2)]
  | _ => some [(8,0)]
theorem root7Node43Domains3_fast_eq : root7Node43Domains3 = expandDomains root7Node43Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node43Domains3 v = expandDomains root7Node43Domains3Fast v from by decide) v
theorem root7Node43Step3Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root7Node43Domains2 root7Node43Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains2 root7Node43Domains3
    root7Node43Domains2Fast root7Node43Domains3Fast
    root7Node43Domains2_fast_eq root7Node43Domains3_fast_eq (by decide)
theorem root7Node43Step3_checked :
    checkReplacement table22 root7Node43Domains2 root7Node43Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node43Step3Chunk0_0_checked, root7Node43Step3Chunk0_1_checked, root7Node43Step3Chunk0_2_checked, root7Node43Step3Chunk0_3_checked, root7Node43Step3Chunk0_4_checked, root7Node43Step3Chunk0_5_checked, root7Node43Step3Chunk1_0_checked, root7Node43Step3Chunk1_1_checked, root7Node43Step3Chunk1_2_checked, root7Node43Step3Chunk1_3_checked, root7Node43Step3Chunk1_4_checked, root7Node43Step3Chunk1_5_checked, root7Node43Step3Chunk2_0_checked, root7Node43Step3Chunk2_1_checked, root7Node43Step3Chunk2_2_checked, root7Node43Step3Chunk2_3_checked, root7Node43Step3Chunk2_4_checked, root7Node43Step3Chunk2_5_checked, root7Node43Step3Chunk3_0_checked, root7Node43Step3Chunk3_1_checked, root7Node43Step3Chunk3_2_checked, root7Node43Step3Chunk3_3_checked, root7Node43Step3Chunk3_4_checked, root7Node43Step3Chunk3_5_checked, root7Node43Step3Chunk4_0_checked, root7Node43Step3Chunk4_1_checked, root7Node43Step3Chunk4_2_checked, root7Node43Step3Chunk4_3_checked, root7Node43Step3Chunk4_4_checked, root7Node43Step3Chunk4_5_checked, root7Node43Step3Chunk5_0_checked, root7Node43Step3Chunk5_1_checked, root7Node43Step3Chunk5_2_checked, root7Node43Step3Chunk5_3_checked, root7Node43Step3Chunk5_4_checked, root7Node43Step3Chunk5_5_checked, root7Node43Step3Chunk6_0_checked, root7Node43Step3Chunk6_1_checked, root7Node43Step3Chunk6_2_checked, root7Node43Step3Chunk6_3_checked, root7Node43Step3Chunk6_4_checked, root7Node43Step3Chunk6_5_checked, root7Node43Step3Chunk7_0_checked, root7Node43Step3Chunk7_1_checked, root7Node43Step3Chunk7_2_checked, root7Node43Step3Chunk7_3_checked, root7Node43Step3Chunk7_4_checked, root7Node43Step3Chunk7_5_checked, root7Node43Step3Chunk8_0_checked, root7Node43Step3Chunk8_1_checked, root7Node43Step3Chunk8_2_checked, root7Node43Step3Chunk8_3_checked, root7Node43Step3Chunk8_4_checked, root7Node43Step3Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node43Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node43Domains3 (.output 21) = true := by decide
def root7Node44Domains0 : Domains 37 State := restrict root7Node0Domains4 6 (1,3)
def root7Node44Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 1 => some [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 2 => some [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 3 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 4 => some [(0,5),(1,2),(6,2),(7,2)]
  | 5 => some [(2,4),(4,4),(7,4),(8,4)]
  | 6 => some [(1,3)]
  | 7 => some [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 8 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 9 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5),(6,5)]
  | 12 => some [(0,4),(6,1)]
  | 13 => some [(3,4),(4,1),(5,1),(5,4),(8,1)]
  | 14 => some [(0,0),(0,1),(0,2),(1,4),(6,3),(6,4),(6,5)]
  | 15 => some [(4,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(5,2),(5,5),(7,5),(8,5)]
  | 21 => some [(0,3),(1,0),(1,1),(3,0),(5,0),(6,0),(6,1),(7,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2),(8,4)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node44Domains0_fast_eq : root7Node44Domains0 = expandDomains root7Node44Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node44Domains0 v = expandDomains root7Node44Domains0Fast v from by decide) v
def root7Node44Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 1 => [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 2 => [(4,1),(7,5),(8,5)]
  | 3 => [(0,2),(0,3),(1,0),(6,0)]
  | 4 => [(0,5),(1,2),(6,2),(7,2)]
  | 5 => [(2,4),(4,4),(7,4),(8,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(5,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4),(5,4)]
  | 14 => [(0,0),(1,4),(6,3),(6,4)]
  | 15 => [(4,2),(7,0),(8,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,0),(6,1)]
  | 22 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(4,2),(7,2),(8,2)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node44Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 1 => some [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 2 => some [(4,1),(7,5),(8,5)]
  | 3 => some [(0,2),(0,3),(1,0),(6,0)]
  | 4 => some [(0,5),(1,2),(6,2),(7,2)]
  | 5 => some [(2,4),(4,4),(7,4),(8,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(5,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(1,4),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,0),(6,1)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,2),(8,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node44Domains1_fast_eq : root7Node44Domains1 = expandDomains root7Node44Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node44Domains1 v = expandDomains root7Node44Domains1Fast v from by decide) v
theorem root7Node44Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1_checked :
    checkReplacement table13 root7Node44Domains0 root7Node44Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node44Step1Chunk0_0_checked, root7Node44Step1Chunk0_1_checked, root7Node44Step1Chunk0_2_checked, root7Node44Step1Chunk0_3_checked, root7Node44Step1Chunk0_4_checked, root7Node44Step1Chunk0_5_checked, root7Node44Step1Chunk1_0_checked, root7Node44Step1Chunk1_1_checked, root7Node44Step1Chunk1_2_checked, root7Node44Step1Chunk1_3_checked, root7Node44Step1Chunk1_4_checked, root7Node44Step1Chunk1_5_checked, root7Node44Step1Chunk2_0_checked, root7Node44Step1Chunk2_1_checked, root7Node44Step1Chunk2_2_checked, root7Node44Step1Chunk2_3_checked, root7Node44Step1Chunk2_4_checked, root7Node44Step1Chunk2_5_checked, root7Node44Step1Chunk3_0_checked, root7Node44Step1Chunk3_1_checked, root7Node44Step1Chunk3_2_checked, root7Node44Step1Chunk3_3_checked, root7Node44Step1Chunk3_4_checked, root7Node44Step1Chunk3_5_checked, root7Node44Step1Chunk4_0_checked, root7Node44Step1Chunk4_1_checked, root7Node44Step1Chunk4_2_checked, root7Node44Step1Chunk4_3_checked, root7Node44Step1Chunk4_4_checked, root7Node44Step1Chunk4_5_checked, root7Node44Step1Chunk5_0_checked, root7Node44Step1Chunk5_1_checked, root7Node44Step1Chunk5_2_checked, root7Node44Step1Chunk5_3_checked, root7Node44Step1Chunk5_4_checked, root7Node44Step1Chunk5_5_checked, root7Node44Step1Chunk6_0_checked, root7Node44Step1Chunk6_1_checked, root7Node44Step1Chunk6_2_checked, root7Node44Step1Chunk6_3_checked, root7Node44Step1Chunk6_4_checked, root7Node44Step1Chunk6_5_checked, root7Node44Step1Chunk7_0_checked, root7Node44Step1Chunk7_1_checked, root7Node44Step1Chunk7_2_checked, root7Node44Step1Chunk7_3_checked, root7Node44Step1Chunk7_4_checked, root7Node44Step1Chunk7_5_checked, root7Node44Step1Chunk8_0_checked, root7Node44Step1Chunk8_1_checked, root7Node44Step1Chunk8_2_checked, root7Node44Step1Chunk8_3_checked, root7Node44Step1Chunk8_4_checked, root7Node44Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
