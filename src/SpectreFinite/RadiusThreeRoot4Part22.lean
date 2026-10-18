module

public import SpectreFinite.RadiusThreeRoot4Part21
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable25
public import SpectreFinite.RadiusThreeTable30
public import SpectreFinite.RadiusThreeTable9

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node37Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(3,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(6,4)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,3)]
  | 22 => [(1,5)]
  | 23 => [(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0)]
  | 29 => [(8,3)]
  | 30 => [(5,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1)]
  | 33 => [(1,4)]
  | 34 => [(0,5)]
  | 35 => [(4,4)]
  | _ => [(0,0)]
def root4Node37Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(3,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(6,4)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(1,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(4,4)]
  | _ => some [(0,0)]
theorem root4Node37Domains2_fast_eq : root4Node37Domains2 = expandDomains root4Node37Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node37Domains2 v = expandDomains root4Node37Domains2Fast v from by decide) v
theorem root4Node37Step2Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root4Node37Domains1 root4Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains1 root4Node37Domains2
    root4Node37Domains1Fast root4Node37Domains2Fast
    root4Node37Domains1_fast_eq root4Node37Domains2_fast_eq (by decide)
theorem root4Node37Step2_checked :
    checkReplacement table30 root4Node37Domains1 root4Node37Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node37Step2Chunk0_0_checked, root4Node37Step2Chunk0_1_checked, root4Node37Step2Chunk0_2_checked, root4Node37Step2Chunk0_3_checked, root4Node37Step2Chunk0_4_checked, root4Node37Step2Chunk0_5_checked, root4Node37Step2Chunk1_0_checked, root4Node37Step2Chunk1_1_checked, root4Node37Step2Chunk1_2_checked, root4Node37Step2Chunk1_3_checked, root4Node37Step2Chunk1_4_checked, root4Node37Step2Chunk1_5_checked, root4Node37Step2Chunk2_0_checked, root4Node37Step2Chunk2_1_checked, root4Node37Step2Chunk2_2_checked, root4Node37Step2Chunk2_3_checked, root4Node37Step2Chunk2_4_checked, root4Node37Step2Chunk2_5_checked, root4Node37Step2Chunk3_0_checked, root4Node37Step2Chunk3_1_checked, root4Node37Step2Chunk3_2_checked, root4Node37Step2Chunk3_3_checked, root4Node37Step2Chunk3_4_checked, root4Node37Step2Chunk3_5_checked, root4Node37Step2Chunk4_0_checked, root4Node37Step2Chunk4_1_checked, root4Node37Step2Chunk4_2_checked, root4Node37Step2Chunk4_3_checked, root4Node37Step2Chunk4_4_checked, root4Node37Step2Chunk4_5_checked, root4Node37Step2Chunk5_0_checked, root4Node37Step2Chunk5_1_checked, root4Node37Step2Chunk5_2_checked, root4Node37Step2Chunk5_3_checked, root4Node37Step2Chunk5_4_checked, root4Node37Step2Chunk5_5_checked, root4Node37Step2Chunk6_0_checked, root4Node37Step2Chunk6_1_checked, root4Node37Step2Chunk6_2_checked, root4Node37Step2Chunk6_3_checked, root4Node37Step2Chunk6_4_checked, root4Node37Step2Chunk6_5_checked, root4Node37Step2Chunk7_0_checked, root4Node37Step2Chunk7_1_checked, root4Node37Step2Chunk7_2_checked, root4Node37Step2Chunk7_3_checked, root4Node37Step2Chunk7_4_checked, root4Node37Step2Chunk7_5_checked, root4Node37Step2Chunk8_0_checked, root4Node37Step2Chunk8_1_checked, root4Node37Step2Chunk8_2_checked, root4Node37Step2Chunk8_3_checked, root4Node37Step2Chunk8_4_checked, root4Node37Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node37Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node37Domains2 (.output 18) = true := by decide
def root4Node38Domains0 : Domains 37 State := restrict root4Node30Domains1 0 (4,0)
def root4Node38Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(3,1),(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(5,0),(5,3),(8,3)]
  | 10 => some [(4,5),(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(7,4),(8,4)]
  | 16 => some [(0,0),(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(0,2),(1,5)]
  | 23 => some [(1,1),(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(7,0),(8,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5),(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1),(7,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => some [(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(4,0),(5,0),(8,0)]
theorem root4Node38Domains0_fast_eq : root4Node38Domains0 = expandDomains root4Node38Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node38Domains0 v = expandDomains root4Node38Domains0Fast v from by decide) v
def root4Node38Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(5,0),(5,3),(8,0)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(7,0),(8,0)]
  | 29 => [(8,3)]
  | 30 => [(5,5),(8,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1),(7,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5),(1,3),(6,3)]
  | 35 => [(4,4),(7,2),(8,2)]
  | _ => [(0,0),(4,0),(5,0),(8,0)]
def root4Node38Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(7,0),(8,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5),(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1),(7,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => some [(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(4,0),(5,0),(8,0)]
theorem root4Node38Domains1_fast_eq : root4Node38Domains1 = expandDomains root4Node38Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node38Domains1 v = expandDomains root4Node38Domains1Fast v from by decide) v
theorem root4Node38Step1Chunk0_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1_checked :
    checkReplacement table9 root4Node38Domains0 root4Node38Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node38Step1Chunk0_0_checked, root4Node38Step1Chunk0_1_checked, root4Node38Step1Chunk0_2_checked, root4Node38Step1Chunk0_3_checked, root4Node38Step1Chunk0_4_checked, root4Node38Step1Chunk0_5_checked, root4Node38Step1Chunk1_0_checked, root4Node38Step1Chunk1_1_checked, root4Node38Step1Chunk1_2_checked, root4Node38Step1Chunk1_3_checked, root4Node38Step1Chunk1_4_checked, root4Node38Step1Chunk1_5_checked, root4Node38Step1Chunk2_0_checked, root4Node38Step1Chunk2_1_checked, root4Node38Step1Chunk2_2_checked, root4Node38Step1Chunk2_3_checked, root4Node38Step1Chunk2_4_checked, root4Node38Step1Chunk2_5_checked, root4Node38Step1Chunk3_0_checked, root4Node38Step1Chunk3_1_checked, root4Node38Step1Chunk3_2_checked, root4Node38Step1Chunk3_3_checked, root4Node38Step1Chunk3_4_checked, root4Node38Step1Chunk3_5_checked, root4Node38Step1Chunk4_0_checked, root4Node38Step1Chunk4_1_checked, root4Node38Step1Chunk4_2_checked, root4Node38Step1Chunk4_3_checked, root4Node38Step1Chunk4_4_checked, root4Node38Step1Chunk4_5_checked, root4Node38Step1Chunk5_0_checked, root4Node38Step1Chunk5_1_checked, root4Node38Step1Chunk5_2_checked, root4Node38Step1Chunk5_3_checked, root4Node38Step1Chunk5_4_checked, root4Node38Step1Chunk5_5_checked, root4Node38Step1Chunk6_0_checked, root4Node38Step1Chunk6_1_checked, root4Node38Step1Chunk6_2_checked, root4Node38Step1Chunk6_3_checked, root4Node38Step1Chunk6_4_checked, root4Node38Step1Chunk6_5_checked, root4Node38Step1Chunk7_0_checked, root4Node38Step1Chunk7_1_checked, root4Node38Step1Chunk7_2_checked, root4Node38Step1Chunk7_3_checked, root4Node38Step1Chunk7_4_checked, root4Node38Step1Chunk7_5_checked, root4Node38Step1Chunk8_0_checked, root4Node38Step1Chunk8_1_checked, root4Node38Step1Chunk8_2_checked, root4Node38Step1Chunk8_3_checked, root4Node38Step1Chunk8_4_checked, root4Node38Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node38Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(8,0)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,0),(5,3),(8,0)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0),(8,0)]
  | 29 => [(8,3)]
  | 30 => [(5,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5)]
  | 35 => [(4,4)]
  | _ => [(0,0)]
def root4Node38Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0),(8,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5)]
  | 35 => some [(4,4)]
  | _ => some [(0,0)]
theorem root4Node38Domains2_fast_eq : root4Node38Domains2 = expandDomains root4Node38Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node38Domains2 v = expandDomains root4Node38Domains2Fast v from by decide) v
theorem root4Node38Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2_checked :
    checkReplacement table25 root4Node38Domains1 root4Node38Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node38Step2Chunk0_0_checked, root4Node38Step2Chunk0_1_checked, root4Node38Step2Chunk0_2_checked, root4Node38Step2Chunk0_3_checked, root4Node38Step2Chunk0_4_checked, root4Node38Step2Chunk0_5_checked, root4Node38Step2Chunk1_0_checked, root4Node38Step2Chunk1_1_checked, root4Node38Step2Chunk1_2_checked, root4Node38Step2Chunk1_3_checked, root4Node38Step2Chunk1_4_checked, root4Node38Step2Chunk1_5_checked, root4Node38Step2Chunk2_0_checked, root4Node38Step2Chunk2_1_checked, root4Node38Step2Chunk2_2_checked, root4Node38Step2Chunk2_3_checked, root4Node38Step2Chunk2_4_checked, root4Node38Step2Chunk2_5_checked, root4Node38Step2Chunk3_0_checked, root4Node38Step2Chunk3_1_checked, root4Node38Step2Chunk3_2_checked, root4Node38Step2Chunk3_3_checked, root4Node38Step2Chunk3_4_checked, root4Node38Step2Chunk3_5_checked, root4Node38Step2Chunk4_0_checked, root4Node38Step2Chunk4_1_checked, root4Node38Step2Chunk4_2_checked, root4Node38Step2Chunk4_3_checked, root4Node38Step2Chunk4_4_checked, root4Node38Step2Chunk4_5_checked, root4Node38Step2Chunk5_0_checked, root4Node38Step2Chunk5_1_checked, root4Node38Step2Chunk5_2_checked, root4Node38Step2Chunk5_3_checked, root4Node38Step2Chunk5_4_checked, root4Node38Step2Chunk5_5_checked, root4Node38Step2Chunk6_0_checked, root4Node38Step2Chunk6_1_checked, root4Node38Step2Chunk6_2_checked, root4Node38Step2Chunk6_3_checked, root4Node38Step2Chunk6_4_checked, root4Node38Step2Chunk6_5_checked, root4Node38Step2Chunk7_0_checked, root4Node38Step2Chunk7_1_checked, root4Node38Step2Chunk7_2_checked, root4Node38Step2Chunk7_3_checked, root4Node38Step2Chunk7_4_checked, root4Node38Step2Chunk7_5_checked, root4Node38Step2Chunk8_0_checked, root4Node38Step2Chunk8_1_checked, root4Node38Step2Chunk8_2_checked, root4Node38Step2Chunk8_3_checked, root4Node38Step2Chunk8_4_checked, root4Node38Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
