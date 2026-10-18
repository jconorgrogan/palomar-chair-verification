module

public import SpectreFinite.RadiusThreeRoot0Part8
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable0
public import SpectreFinite.RadiusThreeTable17
public import SpectreFinite.RadiusThreeTable3

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node13Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(0,0)]
  | 4 => [(7,5)]
  | 5 => [(6,0)]
  | 6 => [(7,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(1,3)]
  | 10 => [(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(7,0)]
  | 14 => [(8,3)]
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
def root0Node13Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,5)]
  | 5 => some [(6,0)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(1,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(7,0)]
  | 14 => some [(8,3)]
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
theorem root0Node13Domains2_fast_eq : root0Node13Domains2 = expandDomains root0Node13Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node13Domains2 v = expandDomains root0Node13Domains2Fast v from by decide) v
theorem root0Node13Step2Chunk0_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2_checked :
    checkReplacement table3 root0Node13Domains1 root0Node13Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node13Step2Chunk0_0_checked, root0Node13Step2Chunk0_1_checked, root0Node13Step2Chunk0_2_checked, root0Node13Step2Chunk0_3_checked, root0Node13Step2Chunk0_4_checked, root0Node13Step2Chunk0_5_checked, root0Node13Step2Chunk1_0_checked, root0Node13Step2Chunk1_1_checked, root0Node13Step2Chunk1_2_checked, root0Node13Step2Chunk1_3_checked, root0Node13Step2Chunk1_4_checked, root0Node13Step2Chunk1_5_checked, root0Node13Step2Chunk2_0_checked, root0Node13Step2Chunk2_1_checked, root0Node13Step2Chunk2_2_checked, root0Node13Step2Chunk2_3_checked, root0Node13Step2Chunk2_4_checked, root0Node13Step2Chunk2_5_checked, root0Node13Step2Chunk3_0_checked, root0Node13Step2Chunk3_1_checked, root0Node13Step2Chunk3_2_checked, root0Node13Step2Chunk3_3_checked, root0Node13Step2Chunk3_4_checked, root0Node13Step2Chunk3_5_checked, root0Node13Step2Chunk4_0_checked, root0Node13Step2Chunk4_1_checked, root0Node13Step2Chunk4_2_checked, root0Node13Step2Chunk4_3_checked, root0Node13Step2Chunk4_4_checked, root0Node13Step2Chunk4_5_checked, root0Node13Step2Chunk5_0_checked, root0Node13Step2Chunk5_1_checked, root0Node13Step2Chunk5_2_checked, root0Node13Step2Chunk5_3_checked, root0Node13Step2Chunk5_4_checked, root0Node13Step2Chunk5_5_checked, root0Node13Step2Chunk6_0_checked, root0Node13Step2Chunk6_1_checked, root0Node13Step2Chunk6_2_checked, root0Node13Step2Chunk6_3_checked, root0Node13Step2Chunk6_4_checked, root0Node13Step2Chunk6_5_checked, root0Node13Step2Chunk7_0_checked, root0Node13Step2Chunk7_1_checked, root0Node13Step2Chunk7_2_checked, root0Node13Step2Chunk7_3_checked, root0Node13Step2Chunk7_4_checked, root0Node13Step2Chunk7_5_checked, root0Node13Step2Chunk8_0_checked, root0Node13Step2Chunk8_1_checked, root0Node13Step2Chunk8_2_checked, root0Node13Step2Chunk8_3_checked, root0Node13Step2Chunk8_4_checked, root0Node13Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node13Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node13Domains2 (.output 6) = true := by decide
def root0Node14Domains0 : Domains 37 State := restrict root0Node8Domains2 9 (7,3)
def root0Node14Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 9 => some [(7,3)]
  | 10 => some [(5,2),(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(6,4),(6,5)]
  | 16 => some [(0,4),(1,2),(6,2)]
  | 17 => some [(5,4),(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0),(7,0)]
  | 23 => some [(4,3),(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(1,4),(5,0),(5,3)]
  | 29 => some [(0,5),(4,5),(5,5),(8,5)]
  | 30 => some [(2,0),(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,0),(6,3)]
  | 34 => some [(3,1),(4,4),(7,2)]
  | 35 => some [(0,1),(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node14Domains0_fast_eq : root0Node14Domains0 = expandDomains root0Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node14Domains0 v = expandDomains root0Node14Domains0Fast v from by decide) v
def root0Node14Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(2,0),(2,2),(2,4),(4,4),(7,4),(8,4)]
  | 3 => [(0,0),(1,3),(3,3),(7,3)]
  | 4 => [(4,1),(7,5)]
  | 5 => [(0,2),(6,0)]
  | 6 => [(1,1),(3,1),(7,1)]
  | 7 => [(0,1),(1,5),(6,5)]
  | 8 => [(0,4),(6,1),(6,2)]
  | 9 => [(7,3)]
  | 10 => [(5,2),(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(1,0),(7,0)]
  | 14 => [(4,3),(7,1),(8,3)]
  | 15 => [(0,1),(6,4)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(1,3),(6,3),(7,3)]
  | 22 => [(0,3),(1,0)]
  | 23 => [(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(5,1),(8,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => [(5,0),(5,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => [(0,0),(0,5),(6,0),(6,3)]
  | 34 => [(3,1),(4,4),(7,2)]
  | 35 => [(0,1),(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,2),(6,3)]
def root0Node14Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(7,4)]
  | 1 => some [(0,5),(6,2),(6,3)]
  | 2 => some [(2,0),(2,2),(2,4),(4,4),(7,4),(8,4)]
  | 3 => some [(0,0),(1,3),(3,3),(7,3)]
  | 4 => some [(4,1),(7,5)]
  | 5 => some [(0,2),(6,0)]
  | 6 => some [(1,1),(3,1),(7,1)]
  | 7 => some [(0,1),(1,5),(6,5)]
  | 8 => some [(0,4),(6,1),(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2),(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(6,4)]
  | 16 => some [(1,2),(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0)]
  | 23 => some [(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,0),(6,3)]
  | 34 => some [(3,1),(4,4),(7,2)]
  | 35 => some [(0,1),(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node14Domains1_fast_eq : root0Node14Domains1 = expandDomains root0Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node14Domains1 v = expandDomains root0Node14Domains1Fast v from by decide) v
theorem root0Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1_checked :
    checkReplacement table17 root0Node14Domains0 root0Node14Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node14Step1Chunk0_0_checked, root0Node14Step1Chunk0_1_checked, root0Node14Step1Chunk0_2_checked, root0Node14Step1Chunk0_3_checked, root0Node14Step1Chunk0_4_checked, root0Node14Step1Chunk0_5_checked, root0Node14Step1Chunk1_0_checked, root0Node14Step1Chunk1_1_checked, root0Node14Step1Chunk1_2_checked, root0Node14Step1Chunk1_3_checked, root0Node14Step1Chunk1_4_checked, root0Node14Step1Chunk1_5_checked, root0Node14Step1Chunk2_0_checked, root0Node14Step1Chunk2_1_checked, root0Node14Step1Chunk2_2_checked, root0Node14Step1Chunk2_3_checked, root0Node14Step1Chunk2_4_checked, root0Node14Step1Chunk2_5_checked, root0Node14Step1Chunk3_0_checked, root0Node14Step1Chunk3_1_checked, root0Node14Step1Chunk3_2_checked, root0Node14Step1Chunk3_3_checked, root0Node14Step1Chunk3_4_checked, root0Node14Step1Chunk3_5_checked, root0Node14Step1Chunk4_0_checked, root0Node14Step1Chunk4_1_checked, root0Node14Step1Chunk4_2_checked, root0Node14Step1Chunk4_3_checked, root0Node14Step1Chunk4_4_checked, root0Node14Step1Chunk4_5_checked, root0Node14Step1Chunk5_0_checked, root0Node14Step1Chunk5_1_checked, root0Node14Step1Chunk5_2_checked, root0Node14Step1Chunk5_3_checked, root0Node14Step1Chunk5_4_checked, root0Node14Step1Chunk5_5_checked, root0Node14Step1Chunk6_0_checked, root0Node14Step1Chunk6_1_checked, root0Node14Step1Chunk6_2_checked, root0Node14Step1Chunk6_3_checked, root0Node14Step1Chunk6_4_checked, root0Node14Step1Chunk6_5_checked, root0Node14Step1Chunk7_0_checked, root0Node14Step1Chunk7_1_checked, root0Node14Step1Chunk7_2_checked, root0Node14Step1Chunk7_3_checked, root0Node14Step1Chunk7_4_checked, root0Node14Step1Chunk7_5_checked, root0Node14Step1Chunk8_0_checked, root0Node14Step1Chunk8_1_checked, root0Node14Step1Chunk8_2_checked, root0Node14Step1Chunk8_3_checked, root0Node14Step1Chunk8_4_checked, root0Node14Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node14Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,4),(7,4)]
  | 1 => [(0,5),(6,3)]
  | 2 => [(2,0),(2,2),(2,4),(4,4)]
  | 3 => [(0,0),(1,3),(3,3),(7,3)]
  | 4 => [(4,1),(7,5)]
  | 5 => [(0,2),(6,0)]
  | 6 => [(1,1),(3,1),(7,1)]
  | 7 => [(0,1),(1,5),(6,5)]
  | 8 => [(0,4),(6,1),(6,2)]
  | 9 => [(7,3)]
  | 10 => [(5,2),(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(1,0),(7,0)]
  | 14 => [(4,3),(7,1),(8,3)]
  | 15 => [(0,1),(6,4)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(1,3),(6,3),(7,3)]
  | 22 => [(0,3),(1,0)]
  | 23 => [(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(5,1),(8,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => [(5,0),(5,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => [(0,0),(0,5),(6,0),(6,3)]
  | 34 => [(3,1),(4,4),(7,2)]
  | 35 => [(0,1),(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,2),(6,3)]
def root0Node14Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4),(7,4)]
  | 1 => some [(0,5),(6,3)]
  | 2 => some [(2,0),(2,2),(2,4),(4,4)]
  | 3 => some [(0,0),(1,3),(3,3),(7,3)]
  | 4 => some [(4,1),(7,5)]
  | 5 => some [(0,2),(6,0)]
  | 6 => some [(1,1),(3,1),(7,1)]
  | 7 => some [(0,1),(1,5),(6,5)]
  | 8 => some [(0,4),(6,1),(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2),(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(6,4)]
  | 16 => some [(1,2),(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0)]
  | 23 => some [(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,0),(6,3)]
  | 34 => some [(3,1),(4,4),(7,2)]
  | 35 => some [(0,1),(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node14Domains2_fast_eq : root0Node14Domains2 = expandDomains root0Node14Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node14Domains2 v = expandDomains root0Node14Domains2Fast v from by decide) v
theorem root0Node14Step2Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root0Node14Domains1 root0Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains1 root0Node14Domains2
    root0Node14Domains1Fast root0Node14Domains2Fast
    root0Node14Domains1_fast_eq root0Node14Domains2_fast_eq (by decide)
theorem root0Node14Step2_checked :
    checkReplacement table0 root0Node14Domains1 root0Node14Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node14Step2Chunk0_0_checked, root0Node14Step2Chunk0_1_checked, root0Node14Step2Chunk0_2_checked, root0Node14Step2Chunk0_3_checked, root0Node14Step2Chunk0_4_checked, root0Node14Step2Chunk0_5_checked, root0Node14Step2Chunk1_0_checked, root0Node14Step2Chunk1_1_checked, root0Node14Step2Chunk1_2_checked, root0Node14Step2Chunk1_3_checked, root0Node14Step2Chunk1_4_checked, root0Node14Step2Chunk1_5_checked, root0Node14Step2Chunk2_0_checked, root0Node14Step2Chunk2_1_checked, root0Node14Step2Chunk2_2_checked, root0Node14Step2Chunk2_3_checked, root0Node14Step2Chunk2_4_checked, root0Node14Step2Chunk2_5_checked, root0Node14Step2Chunk3_0_checked, root0Node14Step2Chunk3_1_checked, root0Node14Step2Chunk3_2_checked, root0Node14Step2Chunk3_3_checked, root0Node14Step2Chunk3_4_checked, root0Node14Step2Chunk3_5_checked, root0Node14Step2Chunk4_0_checked, root0Node14Step2Chunk4_1_checked, root0Node14Step2Chunk4_2_checked, root0Node14Step2Chunk4_3_checked, root0Node14Step2Chunk4_4_checked, root0Node14Step2Chunk4_5_checked, root0Node14Step2Chunk5_0_checked, root0Node14Step2Chunk5_1_checked, root0Node14Step2Chunk5_2_checked, root0Node14Step2Chunk5_3_checked, root0Node14Step2Chunk5_4_checked, root0Node14Step2Chunk5_5_checked, root0Node14Step2Chunk6_0_checked, root0Node14Step2Chunk6_1_checked, root0Node14Step2Chunk6_2_checked, root0Node14Step2Chunk6_3_checked, root0Node14Step2Chunk6_4_checked, root0Node14Step2Chunk6_5_checked, root0Node14Step2Chunk7_0_checked, root0Node14Step2Chunk7_1_checked, root0Node14Step2Chunk7_2_checked, root0Node14Step2Chunk7_3_checked, root0Node14Step2Chunk7_4_checked, root0Node14Step2Chunk7_5_checked, root0Node14Step2Chunk8_0_checked, root0Node14Step2Chunk8_1_checked, root0Node14Step2Chunk8_2_checked, root0Node14Step2Chunk8_3_checked, root0Node14Step2Chunk8_4_checked, root0Node14Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
