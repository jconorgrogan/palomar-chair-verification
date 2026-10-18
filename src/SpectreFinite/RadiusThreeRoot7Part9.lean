module

public import SpectreFinite.RadiusThreeRoot7Part8
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable24
public import SpectreFinite.RadiusThreeTable6
public import SpectreFinite.RadiusThreeTable9

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node13Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(5,2),(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(1,0),(7,0)]
  | 4 => [(1,2),(6,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(4,0),(7,4)]
  | 9 => [(0,3),(1,0)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(4,1),(5,1),(8,1)]
  | 14 => [(0,1),(0,2),(6,5)]
  | 15 => [(4,2),(8,2)]
  | 16 => [(5,0),(5,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5),(8,5)]
  | 21 => [(1,0),(3,0),(5,0),(7,0)]
  | 22 => [(1,4),(3,4),(5,4),(7,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(4,4),(7,2),(8,2),(8,4)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(7,1),(8,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => [(5,0),(5,3),(7,0),(8,0)]
def root7Node13Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2),(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(1,0),(7,0)]
  | 4 => some [(1,2),(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0),(7,4)]
  | 9 => some [(0,3),(1,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5),(8,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(4,4),(7,2),(8,2),(8,4)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(5,0),(5,3),(7,0),(8,0)]
theorem root7Node13Domains2_fast_eq : root7Node13Domains2 = expandDomains root7Node13Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node13Domains2 v = expandDomains root7Node13Domains2Fast v from by decide) v
theorem root7Node13Step2Chunk0_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_0⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk0_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_1⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk0_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_2⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk0_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_3⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk0_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_4⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk0_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_5⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk1_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_0⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk1_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_1⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk1_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_2⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk1_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_3⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk1_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_4⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk1_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_5⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk2_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_0⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk2_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_1⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk2_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_2⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk2_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_3⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk2_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_4⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk2_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_5⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk3_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_0⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk3_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_1⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk3_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_2⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk3_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_3⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk3_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_4⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk3_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_5⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk4_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_0⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk4_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_1⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk4_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_2⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk4_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_3⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk4_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_4⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk4_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_5⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk5_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_0⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk5_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_1⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk5_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_2⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk5_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_3⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk5_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_4⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk5_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_5⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk6_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_0⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk6_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_1⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk6_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_2⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk6_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_3⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk6_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_4⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk6_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_5⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk7_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_0⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk7_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_1⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk7_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_2⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk7_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_3⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk7_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_4⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk7_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_5⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk8_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_0⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk8_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_1⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk8_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_2⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk8_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_3⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk8_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_4⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2Chunk8_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_5⟩
      root7Node13Domains1 root7Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains1 root7Node13Domains2
    root7Node13Domains1Fast root7Node13Domains2Fast
    root7Node13Domains1_fast_eq root7Node13Domains2_fast_eq (by decide)
theorem root7Node13Step2_checked :
    checkReplacement table9 root7Node13Domains1 root7Node13Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node13Step2Chunk0_0_checked, root7Node13Step2Chunk0_1_checked, root7Node13Step2Chunk0_2_checked, root7Node13Step2Chunk0_3_checked, root7Node13Step2Chunk0_4_checked, root7Node13Step2Chunk0_5_checked, root7Node13Step2Chunk1_0_checked, root7Node13Step2Chunk1_1_checked, root7Node13Step2Chunk1_2_checked, root7Node13Step2Chunk1_3_checked, root7Node13Step2Chunk1_4_checked, root7Node13Step2Chunk1_5_checked, root7Node13Step2Chunk2_0_checked, root7Node13Step2Chunk2_1_checked, root7Node13Step2Chunk2_2_checked, root7Node13Step2Chunk2_3_checked, root7Node13Step2Chunk2_4_checked, root7Node13Step2Chunk2_5_checked, root7Node13Step2Chunk3_0_checked, root7Node13Step2Chunk3_1_checked, root7Node13Step2Chunk3_2_checked, root7Node13Step2Chunk3_3_checked, root7Node13Step2Chunk3_4_checked, root7Node13Step2Chunk3_5_checked, root7Node13Step2Chunk4_0_checked, root7Node13Step2Chunk4_1_checked, root7Node13Step2Chunk4_2_checked, root7Node13Step2Chunk4_3_checked, root7Node13Step2Chunk4_4_checked, root7Node13Step2Chunk4_5_checked, root7Node13Step2Chunk5_0_checked, root7Node13Step2Chunk5_1_checked, root7Node13Step2Chunk5_2_checked, root7Node13Step2Chunk5_3_checked, root7Node13Step2Chunk5_4_checked, root7Node13Step2Chunk5_5_checked, root7Node13Step2Chunk6_0_checked, root7Node13Step2Chunk6_1_checked, root7Node13Step2Chunk6_2_checked, root7Node13Step2Chunk6_3_checked, root7Node13Step2Chunk6_4_checked, root7Node13Step2Chunk6_5_checked, root7Node13Step2Chunk7_0_checked, root7Node13Step2Chunk7_1_checked, root7Node13Step2Chunk7_2_checked, root7Node13Step2Chunk7_3_checked, root7Node13Step2Chunk7_4_checked, root7Node13Step2Chunk7_5_checked, root7Node13Step2Chunk8_0_checked, root7Node13Step2Chunk8_1_checked, root7Node13Step2Chunk8_2_checked, root7Node13Step2Chunk8_3_checked, root7Node13Step2Chunk8_4_checked, root7Node13Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node13Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(5,2),(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(1,0),(7,0)]
  | 4 => [(1,2),(6,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(4,0),(7,4)]
  | 9 => [(0,3),(1,0)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(4,1),(5,1),(8,1)]
  | 14 => [(0,1),(0,2),(6,5)]
  | 15 => [(4,2),(8,2)]
  | 16 => [(5,0),(5,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5),(8,5)]
  | 21 => [(1,0),(3,0),(5,0),(7,0)]
  | 22 => [(1,4),(3,4),(5,4),(7,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(4,4),(7,2),(8,2),(8,4)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(7,1),(8,1)]
  | 33 => [(2,0),(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2)]
  | _ => [(5,0),(5,3),(7,0),(8,0)]
def root7Node13Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2),(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(1,0),(7,0)]
  | 4 => some [(1,2),(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0),(7,4)]
  | 9 => some [(0,3),(1,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5),(8,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(4,4),(7,2),(8,2),(8,4)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2)]
  | _ => some [(5,0),(5,3),(7,0),(8,0)]
theorem root7Node13Domains3_fast_eq : root7Node13Domains3 = expandDomains root7Node13Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node13Domains3 v = expandDomains root7Node13Domains3Fast v from by decide) v
theorem root7Node13Step3Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root7Node13Domains2 root7Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node13Domains2 root7Node13Domains3
    root7Node13Domains2Fast root7Node13Domains3Fast
    root7Node13Domains2_fast_eq root7Node13Domains3_fast_eq (by decide)
theorem root7Node13Step3_checked :
    checkReplacement table24 root7Node13Domains2 root7Node13Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node13Step3Chunk0_0_checked, root7Node13Step3Chunk0_1_checked, root7Node13Step3Chunk0_2_checked, root7Node13Step3Chunk0_3_checked, root7Node13Step3Chunk0_4_checked, root7Node13Step3Chunk0_5_checked, root7Node13Step3Chunk1_0_checked, root7Node13Step3Chunk1_1_checked, root7Node13Step3Chunk1_2_checked, root7Node13Step3Chunk1_3_checked, root7Node13Step3Chunk1_4_checked, root7Node13Step3Chunk1_5_checked, root7Node13Step3Chunk2_0_checked, root7Node13Step3Chunk2_1_checked, root7Node13Step3Chunk2_2_checked, root7Node13Step3Chunk2_3_checked, root7Node13Step3Chunk2_4_checked, root7Node13Step3Chunk2_5_checked, root7Node13Step3Chunk3_0_checked, root7Node13Step3Chunk3_1_checked, root7Node13Step3Chunk3_2_checked, root7Node13Step3Chunk3_3_checked, root7Node13Step3Chunk3_4_checked, root7Node13Step3Chunk3_5_checked, root7Node13Step3Chunk4_0_checked, root7Node13Step3Chunk4_1_checked, root7Node13Step3Chunk4_2_checked, root7Node13Step3Chunk4_3_checked, root7Node13Step3Chunk4_4_checked, root7Node13Step3Chunk4_5_checked, root7Node13Step3Chunk5_0_checked, root7Node13Step3Chunk5_1_checked, root7Node13Step3Chunk5_2_checked, root7Node13Step3Chunk5_3_checked, root7Node13Step3Chunk5_4_checked, root7Node13Step3Chunk5_5_checked, root7Node13Step3Chunk6_0_checked, root7Node13Step3Chunk6_1_checked, root7Node13Step3Chunk6_2_checked, root7Node13Step3Chunk6_3_checked, root7Node13Step3Chunk6_4_checked, root7Node13Step3Chunk6_5_checked, root7Node13Step3Chunk7_0_checked, root7Node13Step3Chunk7_1_checked, root7Node13Step3Chunk7_2_checked, root7Node13Step3Chunk7_3_checked, root7Node13Step3Chunk7_4_checked, root7Node13Step3Chunk7_5_checked, root7Node13Step3Chunk8_0_checked, root7Node13Step3Chunk8_1_checked, root7Node13Step3Chunk8_2_checked, root7Node13Step3Chunk8_3_checked, root7Node13Step3Chunk8_4_checked, root7Node13Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node14Domains0 : Domains 37 State := restrict root7Node13Domains3 0 (5,2)
def root7Node14Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(1,0),(7,0)]
  | 4 => some [(1,2),(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0),(7,4)]
  | 9 => some [(0,3),(1,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5),(8,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(4,4),(7,2),(8,2),(8,4)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2)]
  | _ => some [(5,0),(5,3),(7,0),(8,0)]
theorem root7Node14Domains0_fast_eq : root7Node14Domains0 = expandDomains root7Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node14Domains0 v = expandDomains root7Node14Domains0Fast v from by decide) v
def root7Node14Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(5,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2),(6,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(0,3),(1,0)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1),(0,2),(6,5)]
  | 15 => [(4,2),(8,2)]
  | 16 => [(5,0),(5,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,2),(5,5),(8,5)]
  | 21 => [(1,0),(3,0),(5,0),(7,0)]
  | 22 => [(1,4),(3,4),(5,4),(7,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(4,4),(7,2),(8,2),(8,4)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(7,1),(8,1)]
  | 33 => [(2,0),(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2)]
  | _ => [(5,0),(5,3),(7,0),(8,0)]
def root7Node14Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2),(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(0,3),(1,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,2),(5,5),(8,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(4,4),(7,2),(8,2),(8,4)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2)]
  | _ => some [(5,0),(5,3),(7,0),(8,0)]
theorem root7Node14Domains1_fast_eq : root7Node14Domains1 = expandDomains root7Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node14Domains1 v = expandDomains root7Node14Domains1Fast v from by decide) v
theorem root7Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root7Node14Domains0 root7Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node14Domains0 root7Node14Domains1
    root7Node14Domains0Fast root7Node14Domains1Fast
    root7Node14Domains0_fast_eq root7Node14Domains1_fast_eq (by decide)
theorem root7Node14Step1_checked :
    checkReplacement table6 root7Node14Domains0 root7Node14Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node14Step1Chunk0_0_checked, root7Node14Step1Chunk0_1_checked, root7Node14Step1Chunk0_2_checked, root7Node14Step1Chunk0_3_checked, root7Node14Step1Chunk0_4_checked, root7Node14Step1Chunk0_5_checked, root7Node14Step1Chunk1_0_checked, root7Node14Step1Chunk1_1_checked, root7Node14Step1Chunk1_2_checked, root7Node14Step1Chunk1_3_checked, root7Node14Step1Chunk1_4_checked, root7Node14Step1Chunk1_5_checked, root7Node14Step1Chunk2_0_checked, root7Node14Step1Chunk2_1_checked, root7Node14Step1Chunk2_2_checked, root7Node14Step1Chunk2_3_checked, root7Node14Step1Chunk2_4_checked, root7Node14Step1Chunk2_5_checked, root7Node14Step1Chunk3_0_checked, root7Node14Step1Chunk3_1_checked, root7Node14Step1Chunk3_2_checked, root7Node14Step1Chunk3_3_checked, root7Node14Step1Chunk3_4_checked, root7Node14Step1Chunk3_5_checked, root7Node14Step1Chunk4_0_checked, root7Node14Step1Chunk4_1_checked, root7Node14Step1Chunk4_2_checked, root7Node14Step1Chunk4_3_checked, root7Node14Step1Chunk4_4_checked, root7Node14Step1Chunk4_5_checked, root7Node14Step1Chunk5_0_checked, root7Node14Step1Chunk5_1_checked, root7Node14Step1Chunk5_2_checked, root7Node14Step1Chunk5_3_checked, root7Node14Step1Chunk5_4_checked, root7Node14Step1Chunk5_5_checked, root7Node14Step1Chunk6_0_checked, root7Node14Step1Chunk6_1_checked, root7Node14Step1Chunk6_2_checked, root7Node14Step1Chunk6_3_checked, root7Node14Step1Chunk6_4_checked, root7Node14Step1Chunk6_5_checked, root7Node14Step1Chunk7_0_checked, root7Node14Step1Chunk7_1_checked, root7Node14Step1Chunk7_2_checked, root7Node14Step1Chunk7_3_checked, root7Node14Step1Chunk7_4_checked, root7Node14Step1Chunk7_5_checked, root7Node14Step1Chunk8_0_checked, root7Node14Step1Chunk8_1_checked, root7Node14Step1Chunk8_2_checked, root7Node14Step1Chunk8_3_checked, root7Node14Step1Chunk8_4_checked, root7Node14Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
