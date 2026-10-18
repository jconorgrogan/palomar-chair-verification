module

public import SpectreFinite.RadiusThreeRoot7Part46
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable25
public import SpectreFinite.RadiusThreeTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node73Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0),(6,4)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(6,1)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(7,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node73Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0),(6,4)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(6,1)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node73Domains2_fast_eq : root7Node73Domains2 = expandDomains root7Node73Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node73Domains2 v = expandDomains root7Node73Domains2Fast v from by decide) v
theorem root7Node73Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root7Node73Domains1 root7Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains1 root7Node73Domains2
    root7Node73Domains1Fast root7Node73Domains2Fast
    root7Node73Domains1_fast_eq root7Node73Domains2_fast_eq (by decide)
theorem root7Node73Step2_checked :
    checkReplacement table25 root7Node73Domains1 root7Node73Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node73Step2Chunk0_0_checked, root7Node73Step2Chunk0_1_checked, root7Node73Step2Chunk0_2_checked, root7Node73Step2Chunk0_3_checked, root7Node73Step2Chunk0_4_checked, root7Node73Step2Chunk0_5_checked, root7Node73Step2Chunk1_0_checked, root7Node73Step2Chunk1_1_checked, root7Node73Step2Chunk1_2_checked, root7Node73Step2Chunk1_3_checked, root7Node73Step2Chunk1_4_checked, root7Node73Step2Chunk1_5_checked, root7Node73Step2Chunk2_0_checked, root7Node73Step2Chunk2_1_checked, root7Node73Step2Chunk2_2_checked, root7Node73Step2Chunk2_3_checked, root7Node73Step2Chunk2_4_checked, root7Node73Step2Chunk2_5_checked, root7Node73Step2Chunk3_0_checked, root7Node73Step2Chunk3_1_checked, root7Node73Step2Chunk3_2_checked, root7Node73Step2Chunk3_3_checked, root7Node73Step2Chunk3_4_checked, root7Node73Step2Chunk3_5_checked, root7Node73Step2Chunk4_0_checked, root7Node73Step2Chunk4_1_checked, root7Node73Step2Chunk4_2_checked, root7Node73Step2Chunk4_3_checked, root7Node73Step2Chunk4_4_checked, root7Node73Step2Chunk4_5_checked, root7Node73Step2Chunk5_0_checked, root7Node73Step2Chunk5_1_checked, root7Node73Step2Chunk5_2_checked, root7Node73Step2Chunk5_3_checked, root7Node73Step2Chunk5_4_checked, root7Node73Step2Chunk5_5_checked, root7Node73Step2Chunk6_0_checked, root7Node73Step2Chunk6_1_checked, root7Node73Step2Chunk6_2_checked, root7Node73Step2Chunk6_3_checked, root7Node73Step2Chunk6_4_checked, root7Node73Step2Chunk6_5_checked, root7Node73Step2Chunk7_0_checked, root7Node73Step2Chunk7_1_checked, root7Node73Step2Chunk7_2_checked, root7Node73Step2Chunk7_3_checked, root7Node73Step2Chunk7_4_checked, root7Node73Step2Chunk7_5_checked, root7Node73Step2Chunk8_0_checked, root7Node73Step2Chunk8_1_checked, root7Node73Step2Chunk8_2_checked, root7Node73Step2Chunk8_3_checked, root7Node73Step2Chunk8_4_checked, root7Node73Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node73Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(6,1)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0),(6,4)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(6,1)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(7,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node73Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0),(6,4)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(6,1)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node73Domains3_fast_eq : root7Node73Domains3 = expandDomains root7Node73Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node73Domains3 v = expandDomains root7Node73Domains3Fast v from by decide) v
theorem root7Node73Step3Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root7Node73Domains2 root7Node73Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains2 root7Node73Domains3
    root7Node73Domains2Fast root7Node73Domains3Fast
    root7Node73Domains2_fast_eq root7Node73Domains3_fast_eq (by decide)
theorem root7Node73Step3_checked :
    checkReplacement table5 root7Node73Domains2 root7Node73Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node73Step3Chunk0_0_checked, root7Node73Step3Chunk0_1_checked, root7Node73Step3Chunk0_2_checked, root7Node73Step3Chunk0_3_checked, root7Node73Step3Chunk0_4_checked, root7Node73Step3Chunk0_5_checked, root7Node73Step3Chunk1_0_checked, root7Node73Step3Chunk1_1_checked, root7Node73Step3Chunk1_2_checked, root7Node73Step3Chunk1_3_checked, root7Node73Step3Chunk1_4_checked, root7Node73Step3Chunk1_5_checked, root7Node73Step3Chunk2_0_checked, root7Node73Step3Chunk2_1_checked, root7Node73Step3Chunk2_2_checked, root7Node73Step3Chunk2_3_checked, root7Node73Step3Chunk2_4_checked, root7Node73Step3Chunk2_5_checked, root7Node73Step3Chunk3_0_checked, root7Node73Step3Chunk3_1_checked, root7Node73Step3Chunk3_2_checked, root7Node73Step3Chunk3_3_checked, root7Node73Step3Chunk3_4_checked, root7Node73Step3Chunk3_5_checked, root7Node73Step3Chunk4_0_checked, root7Node73Step3Chunk4_1_checked, root7Node73Step3Chunk4_2_checked, root7Node73Step3Chunk4_3_checked, root7Node73Step3Chunk4_4_checked, root7Node73Step3Chunk4_5_checked, root7Node73Step3Chunk5_0_checked, root7Node73Step3Chunk5_1_checked, root7Node73Step3Chunk5_2_checked, root7Node73Step3Chunk5_3_checked, root7Node73Step3Chunk5_4_checked, root7Node73Step3Chunk5_5_checked, root7Node73Step3Chunk6_0_checked, root7Node73Step3Chunk6_1_checked, root7Node73Step3Chunk6_2_checked, root7Node73Step3Chunk6_3_checked, root7Node73Step3Chunk6_4_checked, root7Node73Step3Chunk6_5_checked, root7Node73Step3Chunk7_0_checked, root7Node73Step3Chunk7_1_checked, root7Node73Step3Chunk7_2_checked, root7Node73Step3Chunk7_3_checked, root7Node73Step3Chunk7_4_checked, root7Node73Step3Chunk7_5_checked, root7Node73Step3Chunk8_0_checked, root7Node73Step3Chunk8_1_checked, root7Node73Step3Chunk8_2_checked, root7Node73Step3Chunk8_3_checked, root7Node73Step3Chunk8_4_checked, root7Node73Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node73Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(6,1)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0),(6,4)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(6,1)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(7,1)]
  | 33 => [(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node73Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0),(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(6,1)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(7,1)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node73Domains4_fast_eq : root7Node73Domains4 = expandDomains root7Node73Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node73Domains4 v = expandDomains root7Node73Domains4Fast v from by decide) v
theorem root7Node73Step4Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root7Node73Domains3 root7Node73Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node73Domains3 root7Node73Domains4
    root7Node73Domains3Fast root7Node73Domains4Fast
    root7Node73Domains3_fast_eq root7Node73Domains4_fast_eq (by decide)
theorem root7Node73Step4_checked :
    checkReplacement table22 root7Node73Domains3 root7Node73Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node73Step4Chunk0_0_checked, root7Node73Step4Chunk0_1_checked, root7Node73Step4Chunk0_2_checked, root7Node73Step4Chunk0_3_checked, root7Node73Step4Chunk0_4_checked, root7Node73Step4Chunk0_5_checked, root7Node73Step4Chunk1_0_checked, root7Node73Step4Chunk1_1_checked, root7Node73Step4Chunk1_2_checked, root7Node73Step4Chunk1_3_checked, root7Node73Step4Chunk1_4_checked, root7Node73Step4Chunk1_5_checked, root7Node73Step4Chunk2_0_checked, root7Node73Step4Chunk2_1_checked, root7Node73Step4Chunk2_2_checked, root7Node73Step4Chunk2_3_checked, root7Node73Step4Chunk2_4_checked, root7Node73Step4Chunk2_5_checked, root7Node73Step4Chunk3_0_checked, root7Node73Step4Chunk3_1_checked, root7Node73Step4Chunk3_2_checked, root7Node73Step4Chunk3_3_checked, root7Node73Step4Chunk3_4_checked, root7Node73Step4Chunk3_5_checked, root7Node73Step4Chunk4_0_checked, root7Node73Step4Chunk4_1_checked, root7Node73Step4Chunk4_2_checked, root7Node73Step4Chunk4_3_checked, root7Node73Step4Chunk4_4_checked, root7Node73Step4Chunk4_5_checked, root7Node73Step4Chunk5_0_checked, root7Node73Step4Chunk5_1_checked, root7Node73Step4Chunk5_2_checked, root7Node73Step4Chunk5_3_checked, root7Node73Step4Chunk5_4_checked, root7Node73Step4Chunk5_5_checked, root7Node73Step4Chunk6_0_checked, root7Node73Step4Chunk6_1_checked, root7Node73Step4Chunk6_2_checked, root7Node73Step4Chunk6_3_checked, root7Node73Step4Chunk6_4_checked, root7Node73Step4Chunk6_5_checked, root7Node73Step4Chunk7_0_checked, root7Node73Step4Chunk7_1_checked, root7Node73Step4Chunk7_2_checked, root7Node73Step4Chunk7_3_checked, root7Node73Step4Chunk7_4_checked, root7Node73Step4Chunk7_5_checked, root7Node73Step4Chunk8_0_checked, root7Node73Step4Chunk8_1_checked, root7Node73Step4Chunk8_2_checked, root7Node73Step4Chunk8_3_checked, root7Node73Step4Chunk8_4_checked, root7Node73Step4Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
