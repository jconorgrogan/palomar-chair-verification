module

public import SpectreFinite.RadiusThreeRoot7Part30
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable25
public import SpectreFinite.RadiusThreeTable30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node45Domains5 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5)]
  | 1 => [(0,3)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5)]
  | 5 => [(2,4)]
  | 6 => [(1,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(2,2),(4,2),(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(7,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,5)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node45Domains5Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4)]
  | 6 => some [(1,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(2,2),(4,2),(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(7,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,5)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node45Domains5_fast_eq : root7Node45Domains5 = expandDomains root7Node45Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node45Domains5 v = expandDomains root7Node45Domains5Fast v from by decide) v
theorem root7Node45Step5Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root7Node45Domains4 root7Node45Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains4 root7Node45Domains5
    root7Node45Domains4Fast root7Node45Domains5Fast
    root7Node45Domains4_fast_eq root7Node45Domains5_fast_eq (by decide)
theorem root7Node45Step5_checked :
    checkReplacement table30 root7Node45Domains4 root7Node45Domains5 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node45Step5Chunk0_0_checked, root7Node45Step5Chunk0_1_checked, root7Node45Step5Chunk0_2_checked, root7Node45Step5Chunk0_3_checked, root7Node45Step5Chunk0_4_checked, root7Node45Step5Chunk0_5_checked, root7Node45Step5Chunk1_0_checked, root7Node45Step5Chunk1_1_checked, root7Node45Step5Chunk1_2_checked, root7Node45Step5Chunk1_3_checked, root7Node45Step5Chunk1_4_checked, root7Node45Step5Chunk1_5_checked, root7Node45Step5Chunk2_0_checked, root7Node45Step5Chunk2_1_checked, root7Node45Step5Chunk2_2_checked, root7Node45Step5Chunk2_3_checked, root7Node45Step5Chunk2_4_checked, root7Node45Step5Chunk2_5_checked, root7Node45Step5Chunk3_0_checked, root7Node45Step5Chunk3_1_checked, root7Node45Step5Chunk3_2_checked, root7Node45Step5Chunk3_3_checked, root7Node45Step5Chunk3_4_checked, root7Node45Step5Chunk3_5_checked, root7Node45Step5Chunk4_0_checked, root7Node45Step5Chunk4_1_checked, root7Node45Step5Chunk4_2_checked, root7Node45Step5Chunk4_3_checked, root7Node45Step5Chunk4_4_checked, root7Node45Step5Chunk4_5_checked, root7Node45Step5Chunk5_0_checked, root7Node45Step5Chunk5_1_checked, root7Node45Step5Chunk5_2_checked, root7Node45Step5Chunk5_3_checked, root7Node45Step5Chunk5_4_checked, root7Node45Step5Chunk5_5_checked, root7Node45Step5Chunk6_0_checked, root7Node45Step5Chunk6_1_checked, root7Node45Step5Chunk6_2_checked, root7Node45Step5Chunk6_3_checked, root7Node45Step5Chunk6_4_checked, root7Node45Step5Chunk6_5_checked, root7Node45Step5Chunk7_0_checked, root7Node45Step5Chunk7_1_checked, root7Node45Step5Chunk7_2_checked, root7Node45Step5Chunk7_3_checked, root7Node45Step5Chunk7_4_checked, root7Node45Step5Chunk7_5_checked, root7Node45Step5Chunk8_0_checked, root7Node45Step5Chunk8_1_checked, root7Node45Step5Chunk8_2_checked, root7Node45Step5Chunk8_3_checked, root7Node45Step5Chunk8_4_checked, root7Node45Step5Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node45Domains6 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5)]
  | 1 => [(0,3)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5)]
  | 5 => [(2,4)]
  | 6 => [(1,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(4,2),(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(7,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,5)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node45Domains6Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4)]
  | 6 => some [(1,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(4,2),(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(7,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,5)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node45Domains6_fast_eq : root7Node45Domains6 = expandDomains root7Node45Domains6Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node45Domains6 v = expandDomains root7Node45Domains6Fast v from by decide) v
theorem root7Node45Step6Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root7Node45Domains5 root7Node45Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains5 root7Node45Domains6
    root7Node45Domains5Fast root7Node45Domains6Fast
    root7Node45Domains5_fast_eq root7Node45Domains6_fast_eq (by decide)
theorem root7Node45Step6_checked :
    checkReplacement table13 root7Node45Domains5 root7Node45Domains6 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node45Step6Chunk0_0_checked, root7Node45Step6Chunk0_1_checked, root7Node45Step6Chunk0_2_checked, root7Node45Step6Chunk0_3_checked, root7Node45Step6Chunk0_4_checked, root7Node45Step6Chunk0_5_checked, root7Node45Step6Chunk1_0_checked, root7Node45Step6Chunk1_1_checked, root7Node45Step6Chunk1_2_checked, root7Node45Step6Chunk1_3_checked, root7Node45Step6Chunk1_4_checked, root7Node45Step6Chunk1_5_checked, root7Node45Step6Chunk2_0_checked, root7Node45Step6Chunk2_1_checked, root7Node45Step6Chunk2_2_checked, root7Node45Step6Chunk2_3_checked, root7Node45Step6Chunk2_4_checked, root7Node45Step6Chunk2_5_checked, root7Node45Step6Chunk3_0_checked, root7Node45Step6Chunk3_1_checked, root7Node45Step6Chunk3_2_checked, root7Node45Step6Chunk3_3_checked, root7Node45Step6Chunk3_4_checked, root7Node45Step6Chunk3_5_checked, root7Node45Step6Chunk4_0_checked, root7Node45Step6Chunk4_1_checked, root7Node45Step6Chunk4_2_checked, root7Node45Step6Chunk4_3_checked, root7Node45Step6Chunk4_4_checked, root7Node45Step6Chunk4_5_checked, root7Node45Step6Chunk5_0_checked, root7Node45Step6Chunk5_1_checked, root7Node45Step6Chunk5_2_checked, root7Node45Step6Chunk5_3_checked, root7Node45Step6Chunk5_4_checked, root7Node45Step6Chunk5_5_checked, root7Node45Step6Chunk6_0_checked, root7Node45Step6Chunk6_1_checked, root7Node45Step6Chunk6_2_checked, root7Node45Step6Chunk6_3_checked, root7Node45Step6Chunk6_4_checked, root7Node45Step6Chunk6_5_checked, root7Node45Step6Chunk7_0_checked, root7Node45Step6Chunk7_1_checked, root7Node45Step6Chunk7_2_checked, root7Node45Step6Chunk7_3_checked, root7Node45Step6Chunk7_4_checked, root7Node45Step6Chunk7_5_checked, root7Node45Step6Chunk8_0_checked, root7Node45Step6Chunk8_1_checked, root7Node45Step6Chunk8_2_checked, root7Node45Step6Chunk8_3_checked, root7Node45Step6Chunk8_4_checked, root7Node45Step6Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node45Domains7 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5)]
  | 1 => [(0,3)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5)]
  | 5 => [(2,4)]
  | 6 => [(1,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3)]
  | 27 => [(4,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(8,1)]
  | 31 => [(6,5)]
  | 32 => [(0,4)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(5,5),(8,5)]
  | _ => [(3,0),(7,0)]
def root7Node45Domains7Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4)]
  | 6 => some [(1,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(8,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5),(8,5)]
  | _ => some [(3,0),(7,0)]
theorem root7Node45Domains7_fast_eq : root7Node45Domains7 = expandDomains root7Node45Domains7Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node45Domains7 v = expandDomains root7Node45Domains7Fast v from by decide) v
theorem root7Node45Step7Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root7Node45Domains6 root7Node45Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains6 root7Node45Domains7
    root7Node45Domains6Fast root7Node45Domains7Fast
    root7Node45Domains6_fast_eq root7Node45Domains7_fast_eq (by decide)
theorem root7Node45Step7_checked :
    checkReplacement table25 root7Node45Domains6 root7Node45Domains7 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node45Step7Chunk0_0_checked, root7Node45Step7Chunk0_1_checked, root7Node45Step7Chunk0_2_checked, root7Node45Step7Chunk0_3_checked, root7Node45Step7Chunk0_4_checked, root7Node45Step7Chunk0_5_checked, root7Node45Step7Chunk1_0_checked, root7Node45Step7Chunk1_1_checked, root7Node45Step7Chunk1_2_checked, root7Node45Step7Chunk1_3_checked, root7Node45Step7Chunk1_4_checked, root7Node45Step7Chunk1_5_checked, root7Node45Step7Chunk2_0_checked, root7Node45Step7Chunk2_1_checked, root7Node45Step7Chunk2_2_checked, root7Node45Step7Chunk2_3_checked, root7Node45Step7Chunk2_4_checked, root7Node45Step7Chunk2_5_checked, root7Node45Step7Chunk3_0_checked, root7Node45Step7Chunk3_1_checked, root7Node45Step7Chunk3_2_checked, root7Node45Step7Chunk3_3_checked, root7Node45Step7Chunk3_4_checked, root7Node45Step7Chunk3_5_checked, root7Node45Step7Chunk4_0_checked, root7Node45Step7Chunk4_1_checked, root7Node45Step7Chunk4_2_checked, root7Node45Step7Chunk4_3_checked, root7Node45Step7Chunk4_4_checked, root7Node45Step7Chunk4_5_checked, root7Node45Step7Chunk5_0_checked, root7Node45Step7Chunk5_1_checked, root7Node45Step7Chunk5_2_checked, root7Node45Step7Chunk5_3_checked, root7Node45Step7Chunk5_4_checked, root7Node45Step7Chunk5_5_checked, root7Node45Step7Chunk6_0_checked, root7Node45Step7Chunk6_1_checked, root7Node45Step7Chunk6_2_checked, root7Node45Step7Chunk6_3_checked, root7Node45Step7Chunk6_4_checked, root7Node45Step7Chunk6_5_checked, root7Node45Step7Chunk7_0_checked, root7Node45Step7Chunk7_1_checked, root7Node45Step7Chunk7_2_checked, root7Node45Step7Chunk7_3_checked, root7Node45Step7Chunk7_4_checked, root7Node45Step7Chunk7_5_checked, root7Node45Step7Chunk8_0_checked, root7Node45Step7Chunk8_1_checked, root7Node45Step7Chunk8_2_checked, root7Node45Step7Chunk8_3_checked, root7Node45Step7Chunk8_4_checked, root7Node45Step7Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
