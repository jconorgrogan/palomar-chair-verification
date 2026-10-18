module

public import SpectreFinite.RadiusThreeRoot5Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable0
public import SpectreFinite.RadiusThreeTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node2Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(5,0),(5,3)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(7,4),(8,4)]
  | 8 => [(0,0),(1,3)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5),(6,5)]
  | 14 => [(0,4),(6,1)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(4,3),(8,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1)]
  | 33 => [(1,4)]
  | 34 => [(0,5)]
  | 35 => [(2,0)]
  | _ => [(7,3)]
def root5Node2Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(4,2),(5,2),(8,2)]
  | 3 => some [(5,0),(5,3)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(7,4),(8,4)]
  | 8 => some [(0,0),(1,3)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5),(6,5)]
  | 14 => some [(0,4),(6,1)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3),(8,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(2,0)]
  | _ => some [(7,3)]
theorem root5Node2Domains2_fast_eq : root5Node2Domains2 = expandDomains root5Node2Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node2Domains2 v = expandDomains root5Node2Domains2Fast v from by decide) v
theorem root5Node2Step2Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2_checked :
    checkReplacement table0 root5Node2Domains1 root5Node2Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node2Step2Chunk0_0_checked, root5Node2Step2Chunk0_1_checked, root5Node2Step2Chunk0_2_checked, root5Node2Step2Chunk0_3_checked, root5Node2Step2Chunk0_4_checked, root5Node2Step2Chunk0_5_checked, root5Node2Step2Chunk1_0_checked, root5Node2Step2Chunk1_1_checked, root5Node2Step2Chunk1_2_checked, root5Node2Step2Chunk1_3_checked, root5Node2Step2Chunk1_4_checked, root5Node2Step2Chunk1_5_checked, root5Node2Step2Chunk2_0_checked, root5Node2Step2Chunk2_1_checked, root5Node2Step2Chunk2_2_checked, root5Node2Step2Chunk2_3_checked, root5Node2Step2Chunk2_4_checked, root5Node2Step2Chunk2_5_checked, root5Node2Step2Chunk3_0_checked, root5Node2Step2Chunk3_1_checked, root5Node2Step2Chunk3_2_checked, root5Node2Step2Chunk3_3_checked, root5Node2Step2Chunk3_4_checked, root5Node2Step2Chunk3_5_checked, root5Node2Step2Chunk4_0_checked, root5Node2Step2Chunk4_1_checked, root5Node2Step2Chunk4_2_checked, root5Node2Step2Chunk4_3_checked, root5Node2Step2Chunk4_4_checked, root5Node2Step2Chunk4_5_checked, root5Node2Step2Chunk5_0_checked, root5Node2Step2Chunk5_1_checked, root5Node2Step2Chunk5_2_checked, root5Node2Step2Chunk5_3_checked, root5Node2Step2Chunk5_4_checked, root5Node2Step2Chunk5_5_checked, root5Node2Step2Chunk6_0_checked, root5Node2Step2Chunk6_1_checked, root5Node2Step2Chunk6_2_checked, root5Node2Step2Chunk6_3_checked, root5Node2Step2Chunk6_4_checked, root5Node2Step2Chunk6_5_checked, root5Node2Step2Chunk7_0_checked, root5Node2Step2Chunk7_1_checked, root5Node2Step2Chunk7_2_checked, root5Node2Step2Chunk7_3_checked, root5Node2Step2Chunk7_4_checked, root5Node2Step2Chunk7_5_checked, root5Node2Step2Chunk8_0_checked, root5Node2Step2Chunk8_1_checked, root5Node2Step2Chunk8_2_checked, root5Node2Step2Chunk8_3_checked, root5Node2Step2Chunk8_4_checked, root5Node2Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node3Domains0 : Domains 37 State := restrict root5Node2Domains2 3 (5,0)
def root5Node3Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(4,2),(5,2),(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(7,4),(8,4)]
  | 8 => some [(0,0),(1,3)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5),(6,5)]
  | 14 => some [(0,4),(6,1)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3),(8,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(2,0)]
  | _ => some [(7,3)]
theorem root5Node3Domains0_fast_eq : root5Node3Domains0 = expandDomains root5Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node3Domains0 v = expandDomains root5Node3Domains0Fast v from by decide) v
def root5Node3Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(5,0)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(0,0)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(8,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1)]
  | 33 => [(1,4)]
  | 34 => [(0,5)]
  | 35 => [(2,0)]
  | _ => [(7,3)]
def root5Node3Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5)]
  | 14 => some [(6,1)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(8,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(2,0)]
  | _ => some [(7,3)]
theorem root5Node3Domains1_fast_eq : root5Node3Domains1 = expandDomains root5Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node3Domains1 v = expandDomains root5Node3Domains1Fast v from by decide) v
theorem root5Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1_checked :
    checkReplacement table8 root5Node3Domains0 root5Node3Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node3Step1Chunk0_0_checked, root5Node3Step1Chunk0_1_checked, root5Node3Step1Chunk0_2_checked, root5Node3Step1Chunk0_3_checked, root5Node3Step1Chunk0_4_checked, root5Node3Step1Chunk0_5_checked, root5Node3Step1Chunk1_0_checked, root5Node3Step1Chunk1_1_checked, root5Node3Step1Chunk1_2_checked, root5Node3Step1Chunk1_3_checked, root5Node3Step1Chunk1_4_checked, root5Node3Step1Chunk1_5_checked, root5Node3Step1Chunk2_0_checked, root5Node3Step1Chunk2_1_checked, root5Node3Step1Chunk2_2_checked, root5Node3Step1Chunk2_3_checked, root5Node3Step1Chunk2_4_checked, root5Node3Step1Chunk2_5_checked, root5Node3Step1Chunk3_0_checked, root5Node3Step1Chunk3_1_checked, root5Node3Step1Chunk3_2_checked, root5Node3Step1Chunk3_3_checked, root5Node3Step1Chunk3_4_checked, root5Node3Step1Chunk3_5_checked, root5Node3Step1Chunk4_0_checked, root5Node3Step1Chunk4_1_checked, root5Node3Step1Chunk4_2_checked, root5Node3Step1Chunk4_3_checked, root5Node3Step1Chunk4_4_checked, root5Node3Step1Chunk4_5_checked, root5Node3Step1Chunk5_0_checked, root5Node3Step1Chunk5_1_checked, root5Node3Step1Chunk5_2_checked, root5Node3Step1Chunk5_3_checked, root5Node3Step1Chunk5_4_checked, root5Node3Step1Chunk5_5_checked, root5Node3Step1Chunk6_0_checked, root5Node3Step1Chunk6_1_checked, root5Node3Step1Chunk6_2_checked, root5Node3Step1Chunk6_3_checked, root5Node3Step1Chunk6_4_checked, root5Node3Step1Chunk6_5_checked, root5Node3Step1Chunk7_0_checked, root5Node3Step1Chunk7_1_checked, root5Node3Step1Chunk7_2_checked, root5Node3Step1Chunk7_3_checked, root5Node3Step1Chunk7_4_checked, root5Node3Step1Chunk7_5_checked, root5Node3Step1Chunk8_0_checked, root5Node3Step1Chunk8_1_checked, root5Node3Step1Chunk8_2_checked, root5Node3Step1Chunk8_3_checked, root5Node3Step1Chunk8_4_checked, root5Node3Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node4Domains0 : Domains 37 State := restrict root5Node3Domains1 2 (5,2)
def root5Node4Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(5,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5)]
  | 14 => some [(6,1)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(8,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(2,0)]
  | _ => some [(7,3)]
theorem root5Node4Domains0_fast_eq : root5Node4Domains0 = expandDomains root5Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node4Domains0 v = expandDomains root5Node4Domains0Fast v from by decide) v
end SpectreFinite.HexSearch.RadiusThree
