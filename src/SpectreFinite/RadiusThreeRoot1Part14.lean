module

public import SpectreFinite.RadiusThreeRoot1Part13
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable26
public import SpectreFinite.RadiusThreeTable30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node25Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5)]
  | 5 => [(2,0)]
  | 6 => [(7,3)]
  | 7 => [(5,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(6,0)]
  | 10 => [(3,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0),(1,4),(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(0,3),(6,0),(6,1)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2),(7,0),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(5,5),(8,5)]
  | _ => [(1,0)]
def root1Node25Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(3,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root1Node25Domains2_fast_eq : root1Node25Domains2 = expandDomains root1Node25Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node25Domains2 v = expandDomains root1Node25Domains2Fast v from by decide) v
theorem root1Node25Step2Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root1Node25Domains1 root1Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains1 root1Node25Domains2
    root1Node25Domains1Fast root1Node25Domains2Fast
    root1Node25Domains1_fast_eq root1Node25Domains2_fast_eq (by decide)
theorem root1Node25Step2_checked :
    checkReplacement table30 root1Node25Domains1 root1Node25Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node25Step2Chunk0_0_checked, root1Node25Step2Chunk0_1_checked, root1Node25Step2Chunk0_2_checked, root1Node25Step2Chunk0_3_checked, root1Node25Step2Chunk0_4_checked, root1Node25Step2Chunk0_5_checked, root1Node25Step2Chunk1_0_checked, root1Node25Step2Chunk1_1_checked, root1Node25Step2Chunk1_2_checked, root1Node25Step2Chunk1_3_checked, root1Node25Step2Chunk1_4_checked, root1Node25Step2Chunk1_5_checked, root1Node25Step2Chunk2_0_checked, root1Node25Step2Chunk2_1_checked, root1Node25Step2Chunk2_2_checked, root1Node25Step2Chunk2_3_checked, root1Node25Step2Chunk2_4_checked, root1Node25Step2Chunk2_5_checked, root1Node25Step2Chunk3_0_checked, root1Node25Step2Chunk3_1_checked, root1Node25Step2Chunk3_2_checked, root1Node25Step2Chunk3_3_checked, root1Node25Step2Chunk3_4_checked, root1Node25Step2Chunk3_5_checked, root1Node25Step2Chunk4_0_checked, root1Node25Step2Chunk4_1_checked, root1Node25Step2Chunk4_2_checked, root1Node25Step2Chunk4_3_checked, root1Node25Step2Chunk4_4_checked, root1Node25Step2Chunk4_5_checked, root1Node25Step2Chunk5_0_checked, root1Node25Step2Chunk5_1_checked, root1Node25Step2Chunk5_2_checked, root1Node25Step2Chunk5_3_checked, root1Node25Step2Chunk5_4_checked, root1Node25Step2Chunk5_5_checked, root1Node25Step2Chunk6_0_checked, root1Node25Step2Chunk6_1_checked, root1Node25Step2Chunk6_2_checked, root1Node25Step2Chunk6_3_checked, root1Node25Step2Chunk6_4_checked, root1Node25Step2Chunk6_5_checked, root1Node25Step2Chunk7_0_checked, root1Node25Step2Chunk7_1_checked, root1Node25Step2Chunk7_2_checked, root1Node25Step2Chunk7_3_checked, root1Node25Step2Chunk7_4_checked, root1Node25Step2Chunk7_5_checked, root1Node25Step2Chunk8_0_checked, root1Node25Step2Chunk8_1_checked, root1Node25Step2Chunk8_2_checked, root1Node25Step2Chunk8_3_checked, root1Node25Step2Chunk8_4_checked, root1Node25Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node25Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5)]
  | 5 => [(2,0)]
  | 6 => [(7,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(6,0)]
  | 10 => [(3,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(5,5),(8,5)]
  | _ => [(1,0)]
def root1Node25Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(3,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root1Node25Domains3_fast_eq : root1Node25Domains3 = expandDomains root1Node25Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node25Domains3 v = expandDomains root1Node25Domains3Fast v from by decide) v
theorem root1Node25Step3Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root1Node25Domains2 root1Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains2 root1Node25Domains3
    root1Node25Domains2Fast root1Node25Domains3Fast
    root1Node25Domains2_fast_eq root1Node25Domains3_fast_eq (by decide)
theorem root1Node25Step3_checked :
    checkReplacement table13 root1Node25Domains2 root1Node25Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node25Step3Chunk0_0_checked, root1Node25Step3Chunk0_1_checked, root1Node25Step3Chunk0_2_checked, root1Node25Step3Chunk0_3_checked, root1Node25Step3Chunk0_4_checked, root1Node25Step3Chunk0_5_checked, root1Node25Step3Chunk1_0_checked, root1Node25Step3Chunk1_1_checked, root1Node25Step3Chunk1_2_checked, root1Node25Step3Chunk1_3_checked, root1Node25Step3Chunk1_4_checked, root1Node25Step3Chunk1_5_checked, root1Node25Step3Chunk2_0_checked, root1Node25Step3Chunk2_1_checked, root1Node25Step3Chunk2_2_checked, root1Node25Step3Chunk2_3_checked, root1Node25Step3Chunk2_4_checked, root1Node25Step3Chunk2_5_checked, root1Node25Step3Chunk3_0_checked, root1Node25Step3Chunk3_1_checked, root1Node25Step3Chunk3_2_checked, root1Node25Step3Chunk3_3_checked, root1Node25Step3Chunk3_4_checked, root1Node25Step3Chunk3_5_checked, root1Node25Step3Chunk4_0_checked, root1Node25Step3Chunk4_1_checked, root1Node25Step3Chunk4_2_checked, root1Node25Step3Chunk4_3_checked, root1Node25Step3Chunk4_4_checked, root1Node25Step3Chunk4_5_checked, root1Node25Step3Chunk5_0_checked, root1Node25Step3Chunk5_1_checked, root1Node25Step3Chunk5_2_checked, root1Node25Step3Chunk5_3_checked, root1Node25Step3Chunk5_4_checked, root1Node25Step3Chunk5_5_checked, root1Node25Step3Chunk6_0_checked, root1Node25Step3Chunk6_1_checked, root1Node25Step3Chunk6_2_checked, root1Node25Step3Chunk6_3_checked, root1Node25Step3Chunk6_4_checked, root1Node25Step3Chunk6_5_checked, root1Node25Step3Chunk7_0_checked, root1Node25Step3Chunk7_1_checked, root1Node25Step3Chunk7_2_checked, root1Node25Step3Chunk7_3_checked, root1Node25Step3Chunk7_4_checked, root1Node25Step3Chunk7_5_checked, root1Node25Step3Chunk8_0_checked, root1Node25Step3Chunk8_1_checked, root1Node25Step3Chunk8_2_checked, root1Node25Step3Chunk8_3_checked, root1Node25Step3Chunk8_4_checked, root1Node25Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node26Domains0 : Domains 37 State := restrict root1Node25Domains3 14 (1,4)
def root1Node26Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(3,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(1,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root1Node26Domains0_fast_eq : root1Node26Domains0 = expandDomains root1Node26Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node26Domains0 v = expandDomains root1Node26Domains0Fast v from by decide) v
def root1Node26Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5)]
  | 5 => [(2,0)]
  | 6 => [(7,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(6,0)]
  | 10 => [(3,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(1,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(8,5)]
  | _ => [(1,0)]
def root1Node26Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(3,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(1,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(1,0)]
theorem root1Node26Domains1_fast_eq : root1Node26Domains1 = expandDomains root1Node26Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node26Domains1 v = expandDomains root1Node26Domains1Fast v from by decide) v
theorem root1Node26Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1_checked :
    checkReplacement table26 root1Node26Domains0 root1Node26Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node26Step1Chunk0_0_checked, root1Node26Step1Chunk0_1_checked, root1Node26Step1Chunk0_2_checked, root1Node26Step1Chunk0_3_checked, root1Node26Step1Chunk0_4_checked, root1Node26Step1Chunk0_5_checked, root1Node26Step1Chunk1_0_checked, root1Node26Step1Chunk1_1_checked, root1Node26Step1Chunk1_2_checked, root1Node26Step1Chunk1_3_checked, root1Node26Step1Chunk1_4_checked, root1Node26Step1Chunk1_5_checked, root1Node26Step1Chunk2_0_checked, root1Node26Step1Chunk2_1_checked, root1Node26Step1Chunk2_2_checked, root1Node26Step1Chunk2_3_checked, root1Node26Step1Chunk2_4_checked, root1Node26Step1Chunk2_5_checked, root1Node26Step1Chunk3_0_checked, root1Node26Step1Chunk3_1_checked, root1Node26Step1Chunk3_2_checked, root1Node26Step1Chunk3_3_checked, root1Node26Step1Chunk3_4_checked, root1Node26Step1Chunk3_5_checked, root1Node26Step1Chunk4_0_checked, root1Node26Step1Chunk4_1_checked, root1Node26Step1Chunk4_2_checked, root1Node26Step1Chunk4_3_checked, root1Node26Step1Chunk4_4_checked, root1Node26Step1Chunk4_5_checked, root1Node26Step1Chunk5_0_checked, root1Node26Step1Chunk5_1_checked, root1Node26Step1Chunk5_2_checked, root1Node26Step1Chunk5_3_checked, root1Node26Step1Chunk5_4_checked, root1Node26Step1Chunk5_5_checked, root1Node26Step1Chunk6_0_checked, root1Node26Step1Chunk6_1_checked, root1Node26Step1Chunk6_2_checked, root1Node26Step1Chunk6_3_checked, root1Node26Step1Chunk6_4_checked, root1Node26Step1Chunk6_5_checked, root1Node26Step1Chunk7_0_checked, root1Node26Step1Chunk7_1_checked, root1Node26Step1Chunk7_2_checked, root1Node26Step1Chunk7_3_checked, root1Node26Step1Chunk7_4_checked, root1Node26Step1Chunk7_5_checked, root1Node26Step1Chunk8_0_checked, root1Node26Step1Chunk8_1_checked, root1Node26Step1Chunk8_2_checked, root1Node26Step1Chunk8_3_checked, root1Node26Step1Chunk8_4_checked, root1Node26Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node26Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node26Domains1 (.output 12) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
