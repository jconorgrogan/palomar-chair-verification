module

public import SpectreFinite.RadiusThreeRoot7Part56
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable15
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node90Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(8,0)]
  | 9 => [(6,1)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(6,4)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(7,4)]
  | 23 => [(6,3)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(2,2),(4,2)]
  | 28 => [(0,2)]
  | 29 => [(1,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node90Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(2,2),(4,2)]
  | 28 => some [(0,2)]
  | 29 => some [(1,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node90Domains2_fast_eq : root7Node90Domains2 = expandDomains root7Node90Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node90Domains2 v = expandDomains root7Node90Domains2Fast v from by decide) v
theorem root7Node90Step2Chunk0_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_0⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk0_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_1⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk0_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_2⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk0_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_3⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk0_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_4⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk0_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_5⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk1_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_0⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk1_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_1⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk1_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_2⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk1_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_3⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk1_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_4⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk1_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_5⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk2_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_0⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk2_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_1⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk2_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_2⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk2_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_3⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk2_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_4⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk2_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_5⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk3_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_0⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk3_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_1⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk3_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_2⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk3_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_3⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk3_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_4⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk3_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_5⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk4_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_0⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk4_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_1⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk4_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_2⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk4_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_3⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk4_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_4⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk4_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_5⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk5_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_0⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk5_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_1⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk5_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_2⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk5_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_3⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk5_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_4⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk5_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_5⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk6_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_0⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk6_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_1⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk6_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_2⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk6_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_3⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk6_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_4⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk6_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_5⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk7_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_0⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk7_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_1⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk7_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_2⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk7_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_3⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk7_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_4⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk7_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_5⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk8_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_0⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk8_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_1⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk8_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_2⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk8_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_3⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk8_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_4⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2Chunk8_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_5⟩
      root7Node90Domains1 root7Node90Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains1 root7Node90Domains2
    root7Node90Domains1Fast root7Node90Domains2Fast
    root7Node90Domains1_fast_eq root7Node90Domains2_fast_eq (by decide)
theorem root7Node90Step2_checked :
    checkReplacement table15 root7Node90Domains1 root7Node90Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node90Step2Chunk0_0_checked, root7Node90Step2Chunk0_1_checked, root7Node90Step2Chunk0_2_checked, root7Node90Step2Chunk0_3_checked, root7Node90Step2Chunk0_4_checked, root7Node90Step2Chunk0_5_checked, root7Node90Step2Chunk1_0_checked, root7Node90Step2Chunk1_1_checked, root7Node90Step2Chunk1_2_checked, root7Node90Step2Chunk1_3_checked, root7Node90Step2Chunk1_4_checked, root7Node90Step2Chunk1_5_checked, root7Node90Step2Chunk2_0_checked, root7Node90Step2Chunk2_1_checked, root7Node90Step2Chunk2_2_checked, root7Node90Step2Chunk2_3_checked, root7Node90Step2Chunk2_4_checked, root7Node90Step2Chunk2_5_checked, root7Node90Step2Chunk3_0_checked, root7Node90Step2Chunk3_1_checked, root7Node90Step2Chunk3_2_checked, root7Node90Step2Chunk3_3_checked, root7Node90Step2Chunk3_4_checked, root7Node90Step2Chunk3_5_checked, root7Node90Step2Chunk4_0_checked, root7Node90Step2Chunk4_1_checked, root7Node90Step2Chunk4_2_checked, root7Node90Step2Chunk4_3_checked, root7Node90Step2Chunk4_4_checked, root7Node90Step2Chunk4_5_checked, root7Node90Step2Chunk5_0_checked, root7Node90Step2Chunk5_1_checked, root7Node90Step2Chunk5_2_checked, root7Node90Step2Chunk5_3_checked, root7Node90Step2Chunk5_4_checked, root7Node90Step2Chunk5_5_checked, root7Node90Step2Chunk6_0_checked, root7Node90Step2Chunk6_1_checked, root7Node90Step2Chunk6_2_checked, root7Node90Step2Chunk6_3_checked, root7Node90Step2Chunk6_4_checked, root7Node90Step2Chunk6_5_checked, root7Node90Step2Chunk7_0_checked, root7Node90Step2Chunk7_1_checked, root7Node90Step2Chunk7_2_checked, root7Node90Step2Chunk7_3_checked, root7Node90Step2Chunk7_4_checked, root7Node90Step2Chunk7_5_checked, root7Node90Step2Chunk8_0_checked, root7Node90Step2Chunk8_1_checked, root7Node90Step2Chunk8_2_checked, root7Node90Step2Chunk8_3_checked, root7Node90Step2Chunk8_4_checked, root7Node90Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node91Domains0 : Domains 37 State := restrict root7Node90Domains2 26 (1,3)
def root7Node91Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3)]
  | 27 => some [(2,2),(4,2)]
  | 28 => some [(0,2)]
  | 29 => some [(1,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node91Domains0_fast_eq : root7Node91Domains0 = expandDomains root7Node91Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node91Domains0 v = expandDomains root7Node91Domains0Fast v from by decide) v
def root7Node91Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(8,0)]
  | 9 => [(6,1)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(6,4)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(7,4)]
  | 23 => [(6,3)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(0,2)]
  | 29 => [(1,1)]
  | 30 => [(8,1)]
  | 31 => [(6,5)]
  | 32 => [(0,4)]
  | 33 => [(8,0)]
  | 34 => [(8,3)]
  | 35 => [(5,5)]
  | _ => [(3,0),(7,0)]
def root7Node91Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(0,2)]
  | 29 => some [(1,1)]
  | 30 => some [(8,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5)]
  | _ => some [(3,0),(7,0)]
theorem root7Node91Domains1_fast_eq : root7Node91Domains1 = expandDomains root7Node91Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node91Domains1 v = expandDomains root7Node91Domains1Fast v from by decide) v
theorem root7Node91Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1_checked :
    checkReplacement table25 root7Node91Domains0 root7Node91Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node91Step1Chunk0_0_checked, root7Node91Step1Chunk0_1_checked, root7Node91Step1Chunk0_2_checked, root7Node91Step1Chunk0_3_checked, root7Node91Step1Chunk0_4_checked, root7Node91Step1Chunk0_5_checked, root7Node91Step1Chunk1_0_checked, root7Node91Step1Chunk1_1_checked, root7Node91Step1Chunk1_2_checked, root7Node91Step1Chunk1_3_checked, root7Node91Step1Chunk1_4_checked, root7Node91Step1Chunk1_5_checked, root7Node91Step1Chunk2_0_checked, root7Node91Step1Chunk2_1_checked, root7Node91Step1Chunk2_2_checked, root7Node91Step1Chunk2_3_checked, root7Node91Step1Chunk2_4_checked, root7Node91Step1Chunk2_5_checked, root7Node91Step1Chunk3_0_checked, root7Node91Step1Chunk3_1_checked, root7Node91Step1Chunk3_2_checked, root7Node91Step1Chunk3_3_checked, root7Node91Step1Chunk3_4_checked, root7Node91Step1Chunk3_5_checked, root7Node91Step1Chunk4_0_checked, root7Node91Step1Chunk4_1_checked, root7Node91Step1Chunk4_2_checked, root7Node91Step1Chunk4_3_checked, root7Node91Step1Chunk4_4_checked, root7Node91Step1Chunk4_5_checked, root7Node91Step1Chunk5_0_checked, root7Node91Step1Chunk5_1_checked, root7Node91Step1Chunk5_2_checked, root7Node91Step1Chunk5_3_checked, root7Node91Step1Chunk5_4_checked, root7Node91Step1Chunk5_5_checked, root7Node91Step1Chunk6_0_checked, root7Node91Step1Chunk6_1_checked, root7Node91Step1Chunk6_2_checked, root7Node91Step1Chunk6_3_checked, root7Node91Step1Chunk6_4_checked, root7Node91Step1Chunk6_5_checked, root7Node91Step1Chunk7_0_checked, root7Node91Step1Chunk7_1_checked, root7Node91Step1Chunk7_2_checked, root7Node91Step1Chunk7_3_checked, root7Node91Step1Chunk7_4_checked, root7Node91Step1Chunk7_5_checked, root7Node91Step1Chunk8_0_checked, root7Node91Step1Chunk8_1_checked, root7Node91Step1Chunk8_2_checked, root7Node91Step1Chunk8_3_checked, root7Node91Step1Chunk8_4_checked, root7Node91Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node92Domains0 : Domains 37 State := restrict root7Node91Domains1 36 (3,0)
def root7Node92Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(0,2)]
  | 29 => some [(1,1)]
  | 30 => some [(8,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5)]
  | _ => some [(3,0)]
theorem root7Node92Domains0_fast_eq : root7Node92Domains0 = expandDomains root7Node92Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node92Domains0 v = expandDomains root7Node92Domains0Fast v from by decide) v
theorem root7Node92Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node92Domains0 (.output 45) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
