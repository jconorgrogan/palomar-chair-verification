module

public import SpectreFinite.RadiusThreeRoot6Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable26
public import SpectreFinite.RadiusThreeTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node1Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5),(6,5)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(5,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => [(4,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(1,0),(4,2),(7,0),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(1,2),(6,2),(7,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(8,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root6Node1Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5),(6,5)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => some [(4,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(1,0),(4,2),(7,0),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root6Node1Domains3_fast_eq : root6Node1Domains3 = expandDomains root6Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node1Domains3 v = expandDomains root6Node1Domains3Fast v from by decide) v
theorem root6Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3_checked :
    checkReplacement table4 root6Node1Domains2 root6Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node1Step3Chunk0_0_checked, root6Node1Step3Chunk0_1_checked, root6Node1Step3Chunk0_2_checked, root6Node1Step3Chunk0_3_checked, root6Node1Step3Chunk0_4_checked, root6Node1Step3Chunk0_5_checked, root6Node1Step3Chunk1_0_checked, root6Node1Step3Chunk1_1_checked, root6Node1Step3Chunk1_2_checked, root6Node1Step3Chunk1_3_checked, root6Node1Step3Chunk1_4_checked, root6Node1Step3Chunk1_5_checked, root6Node1Step3Chunk2_0_checked, root6Node1Step3Chunk2_1_checked, root6Node1Step3Chunk2_2_checked, root6Node1Step3Chunk2_3_checked, root6Node1Step3Chunk2_4_checked, root6Node1Step3Chunk2_5_checked, root6Node1Step3Chunk3_0_checked, root6Node1Step3Chunk3_1_checked, root6Node1Step3Chunk3_2_checked, root6Node1Step3Chunk3_3_checked, root6Node1Step3Chunk3_4_checked, root6Node1Step3Chunk3_5_checked, root6Node1Step3Chunk4_0_checked, root6Node1Step3Chunk4_1_checked, root6Node1Step3Chunk4_2_checked, root6Node1Step3Chunk4_3_checked, root6Node1Step3Chunk4_4_checked, root6Node1Step3Chunk4_5_checked, root6Node1Step3Chunk5_0_checked, root6Node1Step3Chunk5_1_checked, root6Node1Step3Chunk5_2_checked, root6Node1Step3Chunk5_3_checked, root6Node1Step3Chunk5_4_checked, root6Node1Step3Chunk5_5_checked, root6Node1Step3Chunk6_0_checked, root6Node1Step3Chunk6_1_checked, root6Node1Step3Chunk6_2_checked, root6Node1Step3Chunk6_3_checked, root6Node1Step3Chunk6_4_checked, root6Node1Step3Chunk6_5_checked, root6Node1Step3Chunk7_0_checked, root6Node1Step3Chunk7_1_checked, root6Node1Step3Chunk7_2_checked, root6Node1Step3Chunk7_3_checked, root6Node1Step3Chunk7_4_checked, root6Node1Step3Chunk7_5_checked, root6Node1Step3Chunk8_0_checked, root6Node1Step3Chunk8_1_checked, root6Node1Step3Chunk8_2_checked, root6Node1Step3Chunk8_3_checked, root6Node1Step3Chunk8_4_checked, root6Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node1Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5),(6,5)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(5,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(4,4)]
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
  | 35 => [(8,5)]
  | _ => [(1,0)]
def root6Node1Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5),(6,5)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,4)]
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
  | 35 => some [(8,5)]
  | _ => some [(1,0)]
theorem root6Node1Domains4_fast_eq : root6Node1Domains4 = expandDomains root6Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node1Domains4 v = expandDomains root6Node1Domains4Fast v from by decide) v
theorem root6Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4_checked :
    checkReplacement table26 root6Node1Domains3 root6Node1Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node1Step4Chunk0_0_checked, root6Node1Step4Chunk0_1_checked, root6Node1Step4Chunk0_2_checked, root6Node1Step4Chunk0_3_checked, root6Node1Step4Chunk0_4_checked, root6Node1Step4Chunk0_5_checked, root6Node1Step4Chunk1_0_checked, root6Node1Step4Chunk1_1_checked, root6Node1Step4Chunk1_2_checked, root6Node1Step4Chunk1_3_checked, root6Node1Step4Chunk1_4_checked, root6Node1Step4Chunk1_5_checked, root6Node1Step4Chunk2_0_checked, root6Node1Step4Chunk2_1_checked, root6Node1Step4Chunk2_2_checked, root6Node1Step4Chunk2_3_checked, root6Node1Step4Chunk2_4_checked, root6Node1Step4Chunk2_5_checked, root6Node1Step4Chunk3_0_checked, root6Node1Step4Chunk3_1_checked, root6Node1Step4Chunk3_2_checked, root6Node1Step4Chunk3_3_checked, root6Node1Step4Chunk3_4_checked, root6Node1Step4Chunk3_5_checked, root6Node1Step4Chunk4_0_checked, root6Node1Step4Chunk4_1_checked, root6Node1Step4Chunk4_2_checked, root6Node1Step4Chunk4_3_checked, root6Node1Step4Chunk4_4_checked, root6Node1Step4Chunk4_5_checked, root6Node1Step4Chunk5_0_checked, root6Node1Step4Chunk5_1_checked, root6Node1Step4Chunk5_2_checked, root6Node1Step4Chunk5_3_checked, root6Node1Step4Chunk5_4_checked, root6Node1Step4Chunk5_5_checked, root6Node1Step4Chunk6_0_checked, root6Node1Step4Chunk6_1_checked, root6Node1Step4Chunk6_2_checked, root6Node1Step4Chunk6_3_checked, root6Node1Step4Chunk6_4_checked, root6Node1Step4Chunk6_5_checked, root6Node1Step4Chunk7_0_checked, root6Node1Step4Chunk7_1_checked, root6Node1Step4Chunk7_2_checked, root6Node1Step4Chunk7_3_checked, root6Node1Step4Chunk7_4_checked, root6Node1Step4Chunk7_5_checked, root6Node1Step4Chunk8_0_checked, root6Node1Step4Chunk8_1_checked, root6Node1Step4Chunk8_2_checked, root6Node1Step4Chunk8_3_checked, root6Node1Step4Chunk8_4_checked, root6Node1Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node2Domains0 : Domains 37 State := restrict root6Node1Domains4 3 (1,5)
def root6Node2Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,4)]
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
  | 35 => some [(8,5)]
  | _ => some [(1,0)]
theorem root6Node2Domains0_fast_eq : root6Node2Domains0 = expandDomains root6Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node2Domains0 v = expandDomains root6Node2Domains0Fast v from by decide) v
end SpectreFinite.HexSearch.RadiusThree
